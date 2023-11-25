/* ******************************************************************
 * FSE : Finite State Entropy decoder
 * Copyright (c) 2013-2020, Yann Collet, Facebook, Inc.
 *
 *  You can contact the author at :
 *  - FSE source repository : https://github.com/Cyan4973/FiniteStateEntropy
 *  - Public forum : https://groups.google.com/forum/#!forum/lz4c
 *
 * This source code is licensed under both the BSD-style license (found in the
 * LICENSE file in the root directory of this source tree) and the GPLv2 (found
 * in the COPYING file in the root directory of this source tree).
 * You may select, at your option, one of the above-listed licenses.
****************************************************************** */


/* **************************************************************
*  Includes
****************************************************************/
#include <stdlib.h>     /* malloc, free, qsort */
#include <string.h>     /* memcpy, memset */
#include "debug.h"      /* assert */
#include "bitstream.h"
#include "compiler.h"
#define FSE_STATIC_LINKING_ONLY
#include "fse.h"
#include "error_private.h"


/* **************************************************************
*  Error Management
****************************************************************/
#define FSE_isError ERR_isError
#define FSE_STATIC_ASSERT(c) DEBUG_STATIC_ASSERT(c)   /* use only *after* variable declarations */


/* **************************************************************
*  Templates
****************************************************************/
/*
  designed to be included
  for type-specific functions (template emulation in C)
  Objective is to write these functions only once, for improved maintenance
*/

/* safety checks */
#ifndef FSE_FUNCTION_EXTENSION
#  error "FSE_FUNCTION_EXTENSION must be defined"
#endif
#ifndef FSE_FUNCTION_TYPE
#  error "FSE_FUNCTION_TYPE must be defined"
#endif

/* Function names */
#define FSE_CAT(X,Y) X##Y
#define FSE_FUNCTION_NAME(X,Y) FSE_CAT(X,Y)
#define FSE_TYPE_NAME(X,Y) FSE_CAT(X,Y)


/* Function templates */
FSE_DTable* FSE_createDTable (unsigned tableLog)
{
    if (tableLog > FSE_TABLELOG_ABSOLUTE_MAX) tableLog = FSE_TABLELOG_ABSOLUTE_MAX;
    return (FSE_DTable*)malloc( FSE_DTABLE_SIZE_U32(tableLog) * sizeof (U32) );
}

void FSE_freeDTable (FSE_DTable* dt)
{
    free(dt);
}

size_t FSE_buildDTable(FSE_DTable* dt, const short* normalizedCounter, unsigned maxSymbolValue, unsigned tableLog)
{
    void* const tdPtr = dt+1;   /* because *dt is unsigned, 32-bits aligned on 32-bits */
    FSE_DECODE_TYPE* const tableDecode = (FSE_DECODE_TYPE*) (tdPtr);
    U16 symbolNext[FSE_MAX_SYMBOL_VALUE+1];

    U32 const maxSV1 = maxSymbolValue + 1;
    U32 const tableSize = 1 << tableLog;
    U32 highThreshold = tableSize-1;

    /* Sanity Checks */
    if (maxSymbolValue > FSE_MAX_SYMBOL_VALUE) return ERROR(maxSymbolValue_tooLarge);
    if (tableLog > FSE_MAX_TABLELOG) return ERROR(tableLog_tooLarge);

    /* Init, lay down lowprob symbols */
    {   FSE_DTableHeader DTableH;
        DTableH.tableLog = (U16)tableLog;
        DTableH.fastMode = 1;
        {   S16 const largeLimit= (S16)(1 << (tableLog-1));
            U32 s;
            for (s=0; s<maxSV1; s++) {
                if (normalizedCounter[s]==-1) {
                    tableDecode[highThreshold--] = FSE_decode_t_pack(0, s, 0);
                    symbolNext[s] = 1;
                } else {
                    if (normalizedCounter[s] >= largeLimit) DTableH.fastMode=0;
                    symbolNext[s] = normalizedCounter[s];
        }   }   }
        memcpy(dt, &DTableH, sizeof(DTableH));
    }

    /* Spread symbols */
    {   U32 const tableMask = tableSize-1;
        U32 const step = FSE_TABLESTEP(tableSize);
        U32 s, position = 0;
        for (s=0; s<maxSV1; s++) {
            int i;
            for (i=0; i<normalizedCounter[s]; i++) {
				tableDecode[position] = FSE_decode_t_pack(0, s, 0);
                position = (position + step) & tableMask;
                while (position > highThreshold) position = (position + step) & tableMask;   /* lowprob area */
        }   }
        if (position!=0) return ERROR(GENERIC);   /* position must reach all cells once, otherwise normalizedCounter is incorrect */
    }

    /* Build Decoding table */
    {   U32 u;
        for (u=0; u<tableSize; u++) {
            FSE_FUNCTION_TYPE const symbol = (FSE_FUNCTION_TYPE)FSE_decode_t_symbol(tableDecode[u]);
            U32 const nextState = symbolNext[symbol]++;
            U32 nbBits = tableLog - BIT_highbit32(nextState);
            U32 targetU = (nextState << nbBits) - tableSize;
            tableDecode[u] = FSE_decode_t_pack(targetU - u, symbol, nbBits);
    }   }

    return 0;
}


#ifndef FSE_COMMONDEFS_ONLY

/*-*******************************************************
*  Decompression (Byte symbols)
*********************************************************/
size_t FSE_buildDTable_rle (FSE_DTable* dt, BYTE symbolValue)
{
    void* ptr = dt;
    FSE_DTableHeader* const DTableH = (FSE_DTableHeader*)ptr;
    void* dPtr = dt + 1;
    FSE_decode_t* const cell = (FSE_decode_t*)dPtr;

    DTableH->tableLog = 0;
    DTableH->fastMode = 0;

    *cell = FSE_decode_t_pack(0, symbolValue, 0);

    return 0;
}


size_t FSE_buildDTable_raw (FSE_DTable* dt, unsigned nbBits)
{
    void* ptr = dt;
    FSE_DTableHeader* const DTableH = (FSE_DTableHeader*)ptr;
    void* dPtr = dt + 1;
    FSE_decode_t* const dinfo = (FSE_decode_t*)dPtr;
    const unsigned tableSize = 1 << nbBits;
    const unsigned tableMask = tableSize - 1;
    const unsigned maxSV1 = tableMask+1;
    unsigned s;

    /* Sanity checks */
    if (nbBits < 1) return ERROR(GENERIC);         /* min size */

    /* Build Decoding Table */
    DTableH->tableLog = (U16)nbBits;
    DTableH->fastMode = 1;
    for (s=0; s<maxSV1; s++) {
        dinfo[s] = FSE_decode_t_pack(-(int32_t)s, s, nbBits);
    }

    return 0;
}

typedef struct {
    BYTE *op;
    BYTE *olimit;
    FSE_DState_t state1;
    FSE_DState_t state2;
    FSE_DState_t state3;
    FSE_DState_t state4;
    BIT_DStream_t bitD1;
    BIT_DStream_t bitD2;
} FSE_decompress_usingDTable_args;

FORCE_NOINLINE
void FSE_decompress_usingDTable_internal(
    FSE_decompress_usingDTable_args *args)
{
	BIT_DStreamFast_t bitD1, bitD2;

    BYTE *op = args->op;
    FSE_DState_t state1 = args->state1;
    FSE_DState_t state2 = args->state2;
    FSE_DState_t state3 = args->state3;
    FSE_DState_t state4 = args->state4;
    bitD1.bitContainer = args->bitD1.bitContainer;
    bitD1.bitsConsumed = args->bitD1.bitsConsumed;
    bitD1.limitPtr = args->bitD1.limitPtr;
    bitD1.ptr = args->bitD1.ptr;
    bitD2.bitContainer = args->bitD2.bitContainer;
    bitD2.bitsConsumed = args->bitD2.bitsConsumed;
    bitD2.limitPtr = args->bitD2.limitPtr;
    bitD2.ptr = args->bitD2.ptr;

    /* 8 symbols per loop */
    for ( ; ; op += 8) {
        int breakFlag = 0;
        breakFlag |= (BIT_reloadDStreamFastFast(&bitD1)!=BIT_DStream_unfinished);
        breakFlag |= (BIT_reloadDStreamFastFast(&bitD2)!=BIT_DStream_unfinished);
        if (breakFlag) break;

        op[0] = FSE_decodeSymbolFast(&state1, &bitD1);
        op[1] = FSE_decodeSymbolFast(&state2, &bitD2);
        op[2] = FSE_decodeSymbolFast(&state3, &bitD1);
        op[3] = FSE_decodeSymbolFast(&state4, &bitD2);

        op[4] = FSE_decodeSymbolFast(&state1, &bitD1);
        op[5] = FSE_decodeSymbolFast(&state2, &bitD2);
        op[6] = FSE_decodeSymbolFast(&state3, &bitD1);
        op[7] = FSE_decodeSymbolFast(&state4, &bitD2);
    }

    args->op = op;
    args->state1 = state1;
    args->state2 = state2;
    args->state3 = state3;
    args->state4 = state4;
    args->bitD1.bitContainer = bitD1.bitContainer;
    args->bitD1.bitsConsumed = bitD1.bitsConsumed;
    args->bitD1.limitPtr = bitD1.limitPtr;
    args->bitD1.ptr = bitD1.ptr;
    args->bitD2.bitContainer = bitD2.bitContainer;
    args->bitD2.bitsConsumed = bitD2.bitsConsumed;
    args->bitD2.limitPtr = bitD2.limitPtr;
    args->bitD2.ptr = bitD2.ptr;
}

FORCE_NOINLINE
size_t FSE_decompress_usingDTable_generic(
          void* dst, size_t maxDstSize,
    const void* cSrc, size_t cSrcSize,
    const FSE_DTable* dt)
{
    BYTE* const ostart = (BYTE*) dst;
    BYTE* op = ostart;
    BYTE* const omax = op + maxDstSize;
    BYTE* const olimit = omax-7;

    const BYTE* const istart = (const BYTE*) cSrc;

	size_t const length1 = MEM_readLE16(istart);
	size_t const length2 = cSrcSize - (length1 + 2);
	const BYTE* const istart1 = istart + 2;
	const BYTE* const istart2 = istart1 + length1;

	FSE_decompress_usingDTable_args a;

    /* Init */
    CHECK_F(BIT_initDStream(&a.bitD1, istart1, length1));
    CHECK_F(BIT_initDStream(&a.bitD2, istart2, length2));

    FSE_initDState(&a.state1, &a.bitD1, dt);
    FSE_initDState(&a.state2, &a.bitD2, dt);
    FSE_initDState(&a.state3, &a.bitD1, dt);
    FSE_initDState(&a.state4, &a.bitD2, dt);

    a.op = op;
    a.olimit = olimit;

    FSE_decompress_usingDTable_internal(&a);

    op = a.op;
    BIT_reloadDStream(&a.bitD1);
    BIT_reloadDStream(&a.bitD2);

    while (op < omax) {
        *op++ = FSE_decodeSymbol(&a.state1, &a.bitD1);
        BIT_reloadDStream(&a.bitD1);
        *op++ = FSE_decodeSymbol(&a.state2, &a.bitD2);
        BIT_reloadDStream(&a.bitD2);
        *op++ = FSE_decodeSymbol(&a.state3, &a.bitD1);
        BIT_reloadDStream(&a.bitD1);
        *op++ = FSE_decodeSymbol(&a.state4, &a.bitD2);
        BIT_reloadDStream(&a.bitD2);
    }

    return op-ostart;
}


size_t FSE_decompress_usingDTable(void* dst, size_t originalSize,
                            const void* cSrc, size_t cSrcSize,
                            const FSE_DTable* dt)
{
    return FSE_decompress_usingDTable_generic(dst, originalSize, cSrc, cSrcSize, dt);
}


size_t FSE_decompress_wksp(void* dst, size_t dstCapacity, const void* cSrc, size_t cSrcSize, FSE_DTable* workSpace, unsigned maxLog)
{
    const BYTE* const istart = (const BYTE*)cSrc;
    const BYTE* ip = istart;
    short counting[FSE_MAX_SYMBOL_VALUE+1];
    unsigned tableLog;
    unsigned maxSymbolValue = FSE_MAX_SYMBOL_VALUE;

    /* normal FSE decoding mode */
    size_t const NCountLength = FSE_readNCount (counting, &maxSymbolValue, &tableLog, istart, cSrcSize);
    if (FSE_isError(NCountLength)) return NCountLength;
    if (tableLog > maxLog) return ERROR(tableLog_tooLarge);
    assert(NCountLength <= cSrcSize);
    ip += NCountLength;
    cSrcSize -= NCountLength;

    CHECK_F( FSE_buildDTable (workSpace, counting, maxSymbolValue, tableLog) );

    return FSE_decompress_usingDTable (dst, dstCapacity, ip, cSrcSize, workSpace);   /* always return, even if it is an error code */
}


typedef FSE_DTable DTable_max_t[FSE_DTABLE_SIZE_U32(FSE_MAX_TABLELOG)];

size_t FSE_decompress(void* dst, size_t dstCapacity, const void* cSrc, size_t cSrcSize)
{
    DTable_max_t dt;   /* Static analyzer seems unable to understand this table will be properly initialized later */
    return FSE_decompress_wksp(dst, dstCapacity, cSrc, cSrcSize, dt, FSE_MAX_TABLELOG);
}



#endif   /* FSE_COMMONDEFS_ONLY */
