/*
 * Copyright (C) 2015, Leo Ma <begeekmyfriend@gmail.com>
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include <openssl/sha.h>
#include <openssl/err.h>

#include "cuckoo_filter.h"

/* Configuration */
#define ASSOC_WAY      (4)  /* 4-way association */
#define INVALID_OFFSET ((size_t)-1)

/* Cuckoo hash */
typedef  uint32_t cuckoo_tag_t;

// CUCKOO_HASH_LEN == 32 bytes == 4x8 uint32_ts
//
#define cuckoo_hash_lsb(table,key)     ((cuckoo_tag_t)(((uint32_t *)(key))[0] & table->mask_hash))
#define cuckoo_hash_msb(table,key)     ((cuckoo_tag_t)(((uint32_t *)(key))[1] & table->mask_hash))

/* The log entries store key-value pairs on flash and
 * each entry is assumed just one sector size fit.
 */
struct cuckoo_entry {
    uint8_t hash[CUCKOO_HASH_LEN];
};

// fix these - as we use them in the protocol.
enum { AVAILIBLE=0, OCCUPIED=1, DELETED=2, };

struct hash_table {
    struct hash_slot_cache **buckets;
    struct hash_slot_cache *slots;
    size_t slot_num;
    size_t bucket_num;
    uint32_t mask_hash; // bitmask
};

typedef struct cuckoo_ctx_rec {
    size_t cuckcoo_store_size;
    size_t cuckoo_entries;
    size_t limit_verify_bytes; // bytes
    /// uint32_t mask_verify; // bitmask
    // size_t limit_hash_bytes_bytes; // bytes
    
    struct hash_table hash_table;
    uint8_t *cuckcoo_store_base_addr;
} cuckoo_ctx_t;

/* The in-memory hash buckets cache filter keys (which are assumed to be some hash values)
 * via cuckoo hashing function and map them to log entries stored on flash.
 */
struct hash_slot_cache {
    cuckoo_tag_t tag : 30;  /* summary of key  - up to 30 bits from left or right */
    uint32_t status : 2;  /* FSM */
    size_t offset;  /* offset on flash memory */
};

static inline int is_pow_of_2(uint32_t x)
{
    return !(x & (x-1));
}

static inline size_t bitlength(size_t x) {
    int bits = 0;
    for(;x; bits++) x = x >> 1;
    return bits;
}

static inline uint32_t next_pow_of_2(uint32_t x)
{
    if (is_pow_of_2(x))
        return x;
    x |= x>>1;
    x |= x>>2;
    x |= x>>4;
    x |= x>>8;
    x |= x>>16;
    return x + 1;
}

#ifdef CUCKOO_DBG
static void dump_key(uint8_t *sha1)
{
    int i;
    static const char str[] = "0123456789abcdef";
    
    printf("KEY: ");
    for (i = CUCKOO_HASH_LEN-1; i >= 0; i--) {
        putchar(str[sha1[i] >> 4]);
        putchar(str[sha1[i] & 0xf]);
    }
    putchar('\n');
}
#endif

static size_t next_entry_offset(cuckoo_ctx_t * ctx)
{
    uint8_t *append_addr = ctx->cuckcoo_store_base_addr + ctx->cuckoo_entries * sizeof(struct cuckoo_entry);
    
    if ((ctx->cuckoo_entries + 1) * sizeof(struct cuckoo_entry) > ctx->cuckcoo_store_size) {
        return INVALID_OFFSET;
    } else {
        return (uint32_t)(append_addr - ctx->cuckcoo_store_base_addr);
    }
}

static uint8_t *key_verify(cuckoo_ctx_t * ctx, uint8_t *key, size_t offset)
{
    int i;
    uint8_t *read_addr = ctx->cuckcoo_store_base_addr + offset;
    
    for (i = 0; i < ctx->limit_verify_bytes; i++) {
        if (key[i] != *read_addr) {
            return NULL;
        }
        read_addr++;
    }
    return read_addr;
}

static int cuckoo_hash_collide(struct hash_table *table, cuckoo_tag_t *tag, size_t *p_offset)
{
    int i, j, k, alt_cnt;
    uint32_t old_tag[2];
    size_t offset, old_offset;
    struct hash_slot_cache *slot;
    
    /* Kick out the old bucket and move it to the alternative bucket. */
    offset = *p_offset;
    slot = table->buckets[tag[0]];
    old_tag[0] = tag[0];
    old_tag[1] = slot[0].tag;
    old_offset = slot[0].offset;
    slot[0].tag = tag[1];
    slot[0].offset = offset;
    i = 0 ^ 1;
    k = 0;
    alt_cnt = 0;
    
KICK_OUT:
    slot = table->buckets[old_tag[i]];
    for (j = 0; j < ASSOC_WAY; j++) {
        if (
            offset == INVALID_OFFSET &&
            slot[j].status == DELETED) {
            slot[j].status = OCCUPIED;
            slot[j].tag = old_tag[i ^ 1];
            *p_offset = offset = slot[j].offset;
            break;
        } else if (slot[j].status == AVAILIBLE) {
            slot[j].status = OCCUPIED;
            slot[j].tag = old_tag[i ^ 1];
            slot[j].offset = old_offset;
            break;
        }
    }
    
    if (j == ASSOC_WAY) {
        if (++alt_cnt > 512) {
            if (k == ASSOC_WAY - 1) {
                /* Hash table is almost full and needs to be resized */
                return 1;
            } else {
                k++;
            }
        }
        uint32_t tmp_tag = slot[k].tag;
        size_t tmp_offset = slot[k].offset;
        slot[k].tag = old_tag[i ^ 1];
        slot[k].offset = old_offset;
        old_tag[i ^ 1] = tmp_tag;
        old_offset = tmp_offset;
        
        i ^= 1;
        goto KICK_OUT;
    }
    
    return 0;
}

static int cuckoo_hash_get(cuckoo_ctx_t * ctx, struct hash_table *table, uint8_t *key, uint8_t **read_addr)
{
    int i, j;
    uint8_t *addr;
    size_t offset;
    size_t tag[2];
    struct hash_slot_cache *slot;
    
    ///
    tag[0] = cuckoo_hash_lsb(table,key);
    tag[1] = cuckoo_hash_msb(table,key);
    
#ifdef CUCKOO_DBG
    printf("get t0:%x t1:%x\n", tag[0], tag[1]);
    dump_key(key);
#endif
    
    /* Filter the key and verify if it exists. */
    slot = table->buckets[tag[0]];
    for (i = 0; i < ASSOC_WAY; i++) {
        if (cuckoo_hash_msb(table,key) == slot[i].tag) {
            if (slot[i].status == OCCUPIED) {
                offset = slot[i].offset;
                addr = key_verify(ctx, key, offset);
                if (addr != NULL) {
                    if (read_addr != NULL) {
                        *read_addr = addr;
                    }
                    break;
                }
            } else if (slot[i].status == DELETED) {
                printf("Key has been deleted!\n");
                return DELETED;
            }
        }
    }
    
    if (i == ASSOC_WAY) {
        slot = table->buckets[tag[1]];
        for (j = 0; j < ASSOC_WAY; j++) {
            if (cuckoo_hash_lsb(table,key) == slot[j].tag) {
                if (slot[j].status == OCCUPIED) {
                    offset = slot[j].offset;
                    addr = key_verify(ctx, key, offset);
                    if (addr != NULL) {
                        if (read_addr != NULL) {
                            *read_addr = addr;
                        }
                        break;
                    }
                } else if (slot[j].status == DELETED) {
#ifdef CUCKOO_DBG
                    printf("Key has been deleted!\n");
#endif
                    return DELETED;
                }
            }
        }
        if (j == ASSOC_WAY) {
#ifdef CUCKOO_DBG
            printf("Key not exists!\n");
#endif
            return AVAILIBLE;
        }
    }
    
    return OCCUPIED;
}

static int cuckoo_hash_put(cuckoo_ctx_t * ctx, struct hash_table *table, uint8_t *key, size_t *p_offset)
{
    int i, j;
    cuckoo_tag_t tag[2];
    size_t offset;
    struct hash_slot_cache *slot;
    
    tag[0] = cuckoo_hash_lsb(table,key);
    tag[1] = cuckoo_hash_msb(table,key);
    
#ifdef CUCKOO_DBG
    printf("put offset:%x t0:%x t1:%x\n", *p_offset, tag[0], tag[1]);
#endif
    
    /* Insert new key into hash buckets. */
    offset = *p_offset;
    slot = table->buckets[tag[0]];
    for (i = 0; i < ASSOC_WAY; i++) {
        if (offset == INVALID_OFFSET && slot[i].status == DELETED) {
            slot[i].status = OCCUPIED;
            slot[i].tag = cuckoo_hash_msb(table,key);
            *p_offset = offset = slot[i].offset;
            break;
        } else if (slot[i].status == AVAILIBLE) {
            slot[i].status = OCCUPIED;
            slot[i].tag = cuckoo_hash_msb(table, key);
            slot[i].offset = offset;
            break;
        }
    }
    
    if (i == ASSOC_WAY) {
        slot = table->buckets[tag[1]];
        for (j = 0; j < ASSOC_WAY; j++) {
            if (offset == INVALID_OFFSET && slot[j].status == DELETED) {
                slot[j].status = OCCUPIED;
                slot[j].tag = cuckoo_hash_lsb(table,key);
                *p_offset = offset = slot[j].offset;
                break;
            } else if (slot[j].status == AVAILIBLE) {
                slot[j].status = OCCUPIED;
                slot[j].tag = cuckoo_hash_lsb(table,key);
                slot[j].offset = offset;
                break;
            }
        }
        
        if (j == ASSOC_WAY) {
            if (cuckoo_hash_collide(table, tag, p_offset)) {
#ifdef CUCKOO_DBG
                printf("Hash table collision!\n");
#endif
                return -1;
            }
        }
    }
    return 0;
}

static void cuckoo_hash_status_set(struct hash_table *table, uint8_t *key, int status)
{
    uint32_t i, j, tag[2];
    struct hash_slot_cache *slot;
    
    tag[0] = cuckoo_hash_lsb(table,key);
    tag[1] = cuckoo_hash_msb(table,key);
    
#ifdef CUCKOO_DBG
    printf("set status:%d t0:%x t1:%x\n", status, tag[0], tag[1]);
    dump_key(key);
#endif
    
    /* Insert new key into hash buckets. */
    slot = table->buckets[tag[0]];
    for (i = 0; i < ASSOC_WAY; i++) {
        if (cuckoo_hash_msb(table, key) == slot[i].tag) {
            slot[i].status = status;
            return;
        }
    }
    
    if (i == ASSOC_WAY) {
        slot = table->buckets[tag[1]];
        for (j = 0; j < ASSOC_WAY; j++) {
            if (cuckoo_hash_lsb(table, key) == slot[j].tag) {
                slot[j].status = status;
                return;
            }
        }
        
        if (j == ASSOC_WAY) {
#ifdef CUCKOO_DBG
            printf("Key not exists!\n");
#endif
        }
    }
}

static void cuckoo_hash_delete(struct hash_table *table, uint8_t *key)
{
    cuckoo_hash_status_set(table, key, DELETED);
}

static void cuckoo_hash_recover(struct hash_table *table, uint8_t *key)
{
    cuckoo_hash_status_set(table, key, OCCUPIED);
}

static void cuckoo_rehash(cuckoo_ctx_t * ctx, struct hash_table *table)
{
    int i;
    struct hash_table old_table;
#if 0
    printf("Rehash old: %lu + %luKb",
           sizeof(struct hash_slot_cache),
           ctx->hash_table.bucket_num * sizeof(struct hash_slot_cache *)/1024);
#endif
    /* Reallocate hash slots */
    old_table = *table;
    
    table->slot_num *= 2;
    
    table->slots = calloc(table->slot_num, sizeof(struct hash_slot_cache));
    if (table->slots == NULL) {
        table->slots = old_table.slots;
        return;
    }
    /* Reallocate hash buckets associated with slots */
    table->bucket_num *= 2;
    table->mask_hash = table->bucket_num - 1;
    
    table->buckets = malloc(table->bucket_num * sizeof(struct hash_slot_cache *));
    if (table->buckets == NULL) {
        free(table->slots);
        table->slots = old_table.slots;
        table->buckets = old_table.buckets;
        return;
    }
    for (i = 0; i < table->bucket_num; i++) {
        table->buckets[i] = &table->slots[i * ASSOC_WAY];
    }
    printf("Rehash from buckets=%lu to buckets=%lu, slots=%lu key-mask=%x verify=%lu\n",  old_table.bucket_num, table->bucket_num, table->slot_num, table->mask_hash, ctx->limit_verify_bytes);
    
    /* Rehash all hash slots */
    uint8_t *read_addr = ctx->cuckcoo_store_base_addr;
    size_t entries = ctx->cuckoo_entries;
    while (entries--) {
        uint8_t key[CUCKOO_HASH_LEN];
        size_t offset = read_addr - ctx->cuckcoo_store_base_addr;
        for (i = 0; i < CUCKOO_HASH_LEN; i++) {
            key[i] = *read_addr;
            read_addr++;
        }
        /* Duplicated keys in hash table which can cause eternal
         * hashing collision! Be careful of that!
         */
        assert(!cuckoo_hash_put(ctx, table, key, &offset));
        if (cuckoo_hash_get(ctx, &old_table, key, NULL) == DELETED) {
            cuckoo_hash_delete(table, key);
        }
    }
    
#if 0
    printf(", new: %lub + %luKb buckets=%lu slots=%lu depth=%d\n",
           sizeof(struct hash_slot_cache),
           ctx->hash_table.bucket_num * sizeof(struct hash_slot_cache *)/1024,
           ctx->hash_table.bucket_num , ctx->hash_table.slot_num, ASSOC_WAY);
#endif
    
    free(old_table.slots);
    free(old_table.buckets);
}

uint8_t *cuckoo_filter_get(cuckoo_ctx_t * ctx, uint8_t *_key, size_t _klen)
{
    uint8_t *read_addr = (uint8_t *)!0;
  
#ifdef INTERNAL_HASH
    assert(CUCKOO_HASH_LEN == SHA256_DIGEST_LENGTH);
    
    uint8_t key[CUCKOO_HASH_LEN];
    SHA256(_key,_klen,key);
#else
    uint8_t * key = _key;
#endif
    /* Read data from the log entry on flash. */
    if (cuckoo_hash_get(ctx, &(ctx->hash_table), key, &read_addr) != OCCUPIED)
        return NULL;
    
    return read_addr;
}

cuckoo_return_t cuckoo_filter_exists(cuckoo_ctx_t * ctx, uint8_t *_key, size_t _klen)
{
#ifdef INTERNAL_HASH
    assert(CUCKOO_HASH_LEN == SHA256_DIGEST_LENGTH);
    
    uint8_t key[CUCKOO_HASH_LEN];
    SHA256(_key,_klen,key);
#else
    uint8_t * key = _key;
#endif
    if (cuckoo_hash_get(ctx, &(ctx->hash_table), key, NULL) != OCCUPIED)
        return CUCKOO_NOTFOUND;
    
    return CUCKOO_OK;
}

cuckoo_return_t cuckoo_filter_put(cuckoo_ctx_t * ctx, uint8_t *_key, size_t _klen)
{
    #ifdef INTERNAL_HASH
    assert(CUCKOO_HASH_LEN == SHA256_DIGEST_LENGTH);
    
    uint8_t key[CUCKOO_HASH_LEN];
    SHA256(_key,_klen,key);
#else
    uint8_t * key = _key;
#endif
    /* Important: Reject duplicated keys keeping from eternal collision */
    int status = cuckoo_hash_get(ctx, &(ctx->hash_table), key, NULL);
    if (status == OCCUPIED) {
        return 0;
    } else if (status == DELETED) {
        cuckoo_hash_recover(&(ctx->hash_table), key);
    } else {
        /* Find new log entry offset on flash. */
        size_t offset = next_entry_offset(ctx);
        if (offset == INVALID_OFFSET) {
            assert(1);
            return -1;
        }
        
        /* Insert into hash slots */
        if (cuckoo_hash_put(ctx,&(ctx->hash_table), key, &offset) == -1) {
            cuckoo_rehash(ctx,&(ctx->hash_table));
            cuckoo_hash_put(ctx,&(ctx->hash_table), key, &offset);
        }
        if (offset == INVALID_OFFSET) {
            assert(1);
            return -1;
        };
        assert(offset <= ctx->cuckcoo_store_size - sizeof(struct cuckoo_entry));
        /* Add new entry of key-value pair on flash. */
        int i;
        uint8_t *append_addr = ctx->cuckcoo_store_base_addr + offset;
        for (i = 0; i < CUCKOO_HASH_LEN; i++) {
            *append_addr=key[i];
            append_addr++;
        }
        ctx->cuckoo_entries++;
    }
    return 0;
}

static cuckoo_ctx_t * cuckoo_populate_initial(cuckoo_ctx_t * ctx)
{
    ctx->cuckcoo_store_base_addr = malloc(ctx->cuckcoo_store_size);
    if (ctx->cuckcoo_store_base_addr == NULL)
        goto frout;
    
    ctx->hash_table.slots = calloc(ctx->hash_table.slot_num, sizeof(struct hash_slot_cache));
    if (ctx->hash_table.slots == NULL)
        goto frout;
    
    ctx->hash_table.buckets = calloc(ctx->hash_table.bucket_num, sizeof(struct hash_slot_cache *));
    if (ctx->hash_table.buckets == NULL)
        goto frout;
    
    for (int i = 0; i < ctx->hash_table.bucket_num; i++) {
        ctx->hash_table.buckets[i] = &(ctx->hash_table.slots)[i * ASSOC_WAY];
    }
    assert(ctx->hash_table.bucket_num < (1LLU<<32));
    ctx->hash_table.mask_hash = (uint32_t)(ctx->hash_table.bucket_num -1);
    
    return ctx;
frout:
    cuckoo_free(ctx);
    return NULL;
}

cuckoo_ctx_t * cuckoo_filter_init(size_t expected_elements)
{
    cuckoo_ctx_t * ctx = malloc(sizeof(cuckoo_ctx_t));
    if (!ctx)
        return NULL;
    
    if (expected_elements < 64) expected_elements = 64;
    
    size_t size = expected_elements * sizeof(struct cuckoo_entry);
    
    size = next_pow_of_2((size + 1));
    
    bzero(ctx,sizeof(cuckoo_ctx_t));
    ctx->cuckcoo_store_size = size;
    
    ctx->hash_table.slot_num = size / sizeof(struct cuckoo_entry) / 4;
    ctx->hash_table.bucket_num = ctx->hash_table.slot_num / ASSOC_WAY;
    
    ctx->limit_verify_bytes = CUCKOO_HASH_LEN;
    
    return cuckoo_populate_initial(ctx);
}

cuckoo_ctx_t * cuckoo_filter_init_from_file(uint8_t * inbuff, size_t leninbuf) {
    uint8_t *p = inbuff;
    
    cuckoo_file_hdr * hdr = (cuckoo_file_hdr *)inbuff;
    p += sizeof(cuckoo_file_hdr);
    
    if (ntohl(hdr->magic) != CUCKOO_MAGIC)
        return NULL;
    if ((hdr->magic & 0xF) == (CUCKOO_MAJOR<<4))
        return NULL;
    if (hdr->depth != ASSOC_WAY)
        return NULL;
    
    cuckoo_ctx_t * ctx = malloc(sizeof(cuckoo_ctx_t));
    if (!ctx)
        return NULL;
    
    bzero(ctx,sizeof(cuckoo_ctx_t));
    
    ctx->hash_table.slot_num = ntohl(hdr->slot_num);
    ctx->hash_table.bucket_num = ntohl(hdr->bucket_num);
    
    ctx->limit_verify_bytes = (hdr->bits_verify+1)/8;
    ctx->cuckcoo_store_size = ctx->hash_table.slot_num * sizeof(struct cuckoo_entry);
    
    assert(next_pow_of_2(ctx->hash_table.bucket_num) == ctx->hash_table.bucket_num);
    
    ctx->hash_table.bucket_num = next_pow_of_2(ctx->hash_table.bucket_num);
    ctx->hash_table.mask_hash = ctx->hash_table.bucket_num -1;
    
    
    assert(hdr->bits_hash == bitlength(ctx->hash_table.bucket_num-1));
    size_t bytes_per_hash = 1 + (1 /* occ. bit */ + hdr->bits_hash)/8;

    assert(ctx->limit_verify_bytes <= CUCKOO_HASH_LEN);
    assert(bytes_per_hash <= 4);

    printf("Read: slots %lu, buckets %lu hash %d bits/%d bytes, verify %d bytes\n",ctx->hash_table.slot_num,ctx->hash_table.bucket_num, hdr->bits_hash, bytes_per_hash, ctx->limit_verify_bytes);
    
    size_t len = sizeof(hdr) + ctx->hash_table.bucket_num * ASSOC_WAY * (bytes_per_hash + ctx->limit_verify_bytes);
    
    assert(len <= leninbuf);
    
    if (cuckoo_populate_initial(ctx) == NULL)
        return NULL;
    
    for(size_t i = 0; i < ctx->hash_table.bucket_num; i++) {
        struct hash_slot_cache *slot = ctx->hash_table.buckets[i];
        for (int j = 0; j < ASSOC_WAY; j++) {
            // printf(" %p %x\n", p-inbuff, *(uint32_t*)p);
            uint32_t vw = 0;
            for(int k = 0; k < bytes_per_hash; k++)
                ((uint8_t *)&vw)[ k + 4 - bytes_per_hash] = p[k];
                        
            uint32_t v = ntohl(vw);
            p += bytes_per_hash;

            slot[j].status = (v & 1 ) ? OCCUPIED : AVAILIBLE;
            slot[j].tag = v>>1;
            
            slot[j].offset = next_entry_offset(ctx);
            assert(slot[j].offset != INVALID_OFFSET);
            if (slot[j].offset == INVALID_OFFSET)
                return NULL;
            
            uint8_t *q = ctx->cuckcoo_store_base_addr + slot[j].offset;
            bzero(q,CUCKOO_HASH_LEN);
            memcpy(q,p,ctx->limit_verify_bytes);
            ctx->cuckoo_entries++;
            p+=ctx->limit_verify_bytes;
        };
    };
    printf("Read %lu, expected %lu = %d\n", p-inbuff,leninbuf, (int)(p-inbuff-leninbuf));
    
    assert(p-inbuff == leninbuf);
    
    return ctx;
}

cuckoo_return_t cuckoo_filter_serialize(cuckoo_ctx_t * ctx, uint8_t * outbuffOrNull, size_t * lenoutbuf) {
    cuckoo_file_hdr hdr = {
        .magic = htonl(CUCKOO_MAGIC),
        .version = CUCKOO_VERSION,
        .depth = ASSOC_WAY,
        .bits_hash = bitlength(ctx->hash_table.bucket_num-1),
        .bits_verify = ctx->limit_verify_bytes * 8,
        .slot_num = htonl((uint32_t) ctx-> hash_table.slot_num),
        .bucket_num =htonl((uint32_t) ctx-> hash_table.bucket_num),
    };
    
    ctx->limit_verify_bytes = 2 + (bitlength(ctx->hash_table.bucket_num-1)>>3);
    assert(ctx->limit_verify_bytes<= ctx->limit_verify_bytes);
    
    size_t bytes_per_hash = 1 + bitlength(1 /* occ. status */ + ctx->hash_table.bucket_num)/8;
    size_t len = sizeof(hdr) + ctx->hash_table.bucket_num * ASSOC_WAY * (bytes_per_hash + ctx->limit_verify_bytes);
    
    if (outbuffOrNull == NULL) {
        *lenoutbuf = len;
        return CUCKOO_OK;
    };

    bzero(outbuffOrNull, *lenoutbuf);
    uint8_t * p = outbuffOrNull;
    memcpy(p, &hdr, sizeof(hdr));
    p += sizeof(hdr);
    
    size_t occ = 0;
    for(size_t i = 0; i < ctx->hash_table.bucket_num; i++) {
        struct hash_slot_cache *slot = ctx->hash_table.buckets[i];
        for (int j = 0; j < ASSOC_WAY; j++) {
            uint32_t v = (slot[j].tag)<<1;
            
            switch(slot[j].status) {
                case OCCUPIED:
                    v |= 1; occ++;
                    break;
                case AVAILIBLE:
                case DELETED:
                default:
                    v &= ~1; // clear bottom bit
                    break;
            };
            uint32_t vw = htonl(v);
            for(int k = 0; k < bytes_per_hash; k++)
                p[k] = ((uint8_t *)&vw)[ k + 4 - bytes_per_hash];
                    
            p += bytes_per_hash;

            uint8_t * q = ctx->cuckcoo_store_base_addr + slot[j].offset;
            memcpy(p,q,ctx->limit_verify_bytes);
            p+=ctx->limit_verify_bytes;
            
        }; // ASSOC_WAY
    }; // buckets
    assert(len == p - outbuffOrNull);
    
    printf("%lu Buckets, %lu Slots, %d way, %d bits,%d bytes/hash, %d bits, %d bytes/verify, 2x %lu + %lu = %lu bits of a %d bit hash revealed - CF load %lu of %lu occupied (%.1f%%)\n",
           ctx->hash_table.bucket_num,
           ctx->hash_table.slot_num,
           ASSOC_WAY,
           bitlength(ctx->hash_table.bucket_num-1), bytes_per_hash,
           8 * ctx->limit_verify_bytes,ctx->limit_verify_bytes,
           bitlength(ctx->hash_table.bucket_num-1),
           ctx->limit_verify_bytes,
           2*(bitlength(ctx->hash_table.bucket_num-1)) + 8 * ctx->limit_verify_bytes,
           CUCKOO_HASH_LEN * 8,
           occ,ctx->hash_table.bucket_num * ASSOC_WAY,
           100.*occ/ctx->hash_table.bucket_num/ASSOC_WAY
           );
    
    
    return CUCKOO_OK;
};


void show_hash_slots(cuckoo_ctx_t * ctx)
{
    int i, j;
    struct hash_table *table = &(ctx->hash_table);
    
    printf("\nList all keys in hash table bucket_num=%lu slot_num=%lu key-mask%x value %d bytes (tag/status/offset):\n",
           table->bucket_num,
           table->slot_num,
           ctx->hash_table.mask_hash, ctx->limit_verify_bytes);
    
    size_t occ = 0;
    for (i = 0; i < table->bucket_num; i++) {
        printf("bucket[%04x]:", i);
        
        struct hash_slot_cache *slot = table->buckets[i];
        for (j = 0; j < ASSOC_WAY; j++) {
            printf("\t%8x/%02x/%08lx/", slot[j].tag, slot[j].status, slot[j].offset);
            if (slot[j].status == OCCUPIED)
                occ++;
            for(int k = 0; k < 8; k++) {
                uint8_t c = (ctx->cuckcoo_store_base_addr +  slot[j].offset)[k];
                printf("%c",isprint(c) ? c : '.');
            };
        }
        printf("\n");
        
    }
    printf("\nOccupied %lu of %lu slots, %.1f%%\n",
           occ, table->bucket_num*ASSOC_WAY, 100.*occ/table->bucket_num/ASSOC_WAY);
}

float cf_loading(cuckoo_ctx_t * ctx) {
    size_t occ = 0;
    int i, j;
    struct hash_table *table = &(ctx->hash_table);
    
    for (i = 0; i < table->bucket_num; i++) {
        struct hash_slot_cache *slot = table->buckets[i];
        for (j = 0; j < ASSOC_WAY; j++) {
            if (slot[j].status == OCCUPIED)
                occ++;
        }
    }
    return 100.*occ/table->bucket_num/ASSOC_WAY;
}


cuckoo_return_t cuckoo_free(cuckoo_ctx_t * ctx) {
    if (ctx) {
        if (ctx->hash_table.buckets )
            free(ctx->hash_table.buckets );
        
        if (ctx->hash_table.slots)
            free(ctx->hash_table.slots);
        
        if (ctx->cuckcoo_store_base_addr)
            free(ctx->cuckcoo_store_base_addr);
        
        free(ctx);
    };
    return CUCKOO_OK;
}
