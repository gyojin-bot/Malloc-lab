/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team5",
    /* First member's full name */
    "Choi Gyojin",
    /* First member's email address */
    "choi1036mk@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
//>>> github upload를 위해 변수 하나 추가했습니다! 이번주도 역시 너무 수고 많으셨어요!! <<<< //
#define review_completed 1

#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             /* Word and header/footer size (bytes) */
#define DSIZE 8             /* Double word size (bytes) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))
#define PUT_ADDRESS(p, adress) (*(char **)(p) = (adress))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp)-WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// >>>> 가용리스트의 이전 블럭과 다음 블럭을 찾아오는 함수를 메크로로 잘 짜신 것 같습니다. <<<<
// >>>> 헤더를 기준으로 얼만큼 떨어진 블럭의 정보를 읽는지 잘 보여서 이해가 잘 됩니다! <<<<
#define PRED_LOC(bp) ((char *)HDRP(bp) + WSIZE)
#define SUCC_LOC(bp) ((char *)HDRP(bp) + DSIZE)
#define PRED(bp) *(char **)(PRED_LOC(bp))
#define SUCC(bp) *(char **)(SUCC_LOC(bp))

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))

/* The only global variable is a pointer to the first block */
static char *heap_listp;
static char *root_succ;


// >>>> 함수 헤드를 미리 선언해주셔서, 아래 코드를 읽을 때 함수들의 위치가 뒤죽박죽이지 않아서 읽기 편했습니다! (저희조는 섞었습니다ㅎㅎ)
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    // >>>> 참고용으로 주어졌던 원래의 코드와 비교해서 볼 때,<<<<
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1)  
    // >>>> 제일 처음 최소한의 공간을 heap에 할당 받아 올 때(92번줄) 가용리스트틀 위한 predecessor와 successor를 위해서 두 칸을 더 할당하고 <<<<
        return -1;
    PUT(heap_listp, 0);                                /* Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue header */
    
    // >>>> 초기화 할 떄, 가용공간에 predecessor와 successor를 먼저 선언해 주신 것으로 보입니다! <<<<
    PUT_ADDRESS(heap_listp + (2 * WSIZE), NULL);       
    PUT_ADDRESS(heap_listp + (3 * WSIZE), NULL);

    PUT(heap_listp + (4 * WSIZE), PACK(2 * DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1));         /* Epilogue header ** when find func, note endpoint */
    heap_listp += 2 * WSIZE;


    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)     // >>>> extend heap 시에 새로운 가용공간이 추가되면서 같은 첫번째 predecessor와 successor가 자동으로 만들어 질 수도 있을 것 같습니다.
                                                    // 100,101줄은 꼭 하지는 않으셨어도 됐지 않았을까? 하는 생각이 들었습니다!
                                                    // 꼭 필요할수도 있어요!!<<<<
        return -1;

    PUT_ADDRESS(SUCC_LOC(heap_listp), NEXT_BLKP(heap_listp));
    /* root PRED */

    return 0;
}

// >>>> 제 코드와 비슷해서 넘어갑니다! 코드 읽기 좋게 띄어쓰기 잘 하신 것 같아요.
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */

    PUT_ADDRESS(PRED_LOC(bp), heap_listp);
    PUT_ADDRESS(SUCC_LOC(bp), SUCC(heap_listp));
    PUT_ADDRESS(PRED_LOC(SUCC(bp)), bp);

    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
// >>>> 여기도 넘어갑니닷!
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL)
    {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc)
    { /* Case 1 */

        // >>>> 참고를 위해 말씀 드리면! 제가 참고했던 explicit 코드들은 전부 coalesce에서 case1은 건드리지 않더라구요! 
        PUT_ADDRESS(SUCC_LOC(bp), SUCC(heap_listp));
        PUT_ADDRESS(PRED_LOC(bp), heap_listp);

        PUT_ADDRESS(PRED_LOC(SUCC(bp)), bp);
        PUT_ADDRESS(SUCC_LOC(heap_listp), bp);

        return bp;
    }

    else if (prev_alloc && !next_alloc)
    { /* Case 2 */

        /* freed block's SUCC & freed block's PRED change */
        PUT_ADDRESS(PRED_LOC(SUCC(NEXT_BLKP(bp))), PRED(NEXT_BLKP(bp)));
        PUT_ADDRESS(SUCC_LOC(PRED(NEXT_BLKP(bp))), SUCC(NEXT_BLKP(bp)));


        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));

        PUT_ADDRESS(SUCC_LOC(bp), SUCC(heap_listp));
        PUT_ADDRESS(PRED_LOC(bp), heap_listp);

        PUT_ADDRESS(PRED_LOC(SUCC(bp)), bp);
        PUT_ADDRESS(SUCC_LOC(heap_listp), bp);
    }

    else if (!prev_alloc && next_alloc)
    { /* Case 3 */

        /* freed block's SUCC & freed block's PRED change */
        PUT_ADDRESS(PRED_LOC(SUCC(PREV_BLKP(bp))), PRED(PREV_BLKP(bp)));
        PUT_ADDRESS(SUCC_LOC(PRED(PREV_BLKP(bp))), SUCC(PREV_BLKP(bp)));


        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);


        PUT_ADDRESS(SUCC_LOC(bp), SUCC(heap_listp));
        PUT_ADDRESS(PRED_LOC(bp), heap_listp);

        PUT_ADDRESS(PRED_LOC(SUCC(bp)), bp);
        PUT_ADDRESS(SUCC_LOC(heap_listp), bp);
    }

    else
    { /* Case 4 */
        PUT_ADDRESS(PRED_LOC(SUCC(SUCC(PREV_BLKP(bp)))), PRED(PREV_BLKP(bp)));
        PUT_ADDRESS(SUCC_LOC(PRED(PREV_BLKP(bp))), SUCC(SUCC(PREV_BLKP(bp))));

        PUT_ADDRESS(PRED_LOC(SUCC(NEXT_BLKP(bp))), PRED(PRED(NEXT_BLKP(bp))));
        PUT_ADDRESS(SUCC_LOC(PRED(PRED(NEXT_BLKP(bp)))), SUCC(NEXT_BLKP(bp)));


        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +
                GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);

        PUT_ADDRESS(SUCC_LOC(bp), SUCC(heap_listp));
        PUT_ADDRESS(PRED_LOC(bp), heap_listp);

        PUT_ADDRESS(PRED_LOC(SUCC(bp)), bp);
        PUT_ADDRESS(SUCC_LOC(heap_listp), bp);
    }

    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(oldptr));

    if (size < copySize)
    {
        copySize = size;
    }

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}



static void *find_fit(size_t asize)
{
    /* next-fit search */
    char *bp;

    // Search from next_fit to the end of the heap
    // >>>> explicit에서 find fit 부분이 가용블럭들만을 읽어가면서 체크해야하는데
    // >>>> heap을 모두 검사하면서 fit을 찾는 부분이 implicit과 유사해 보입니다!!
    // >>>> 가용블럭만 조사하는 것으로 코드를 좀 바꿔야 하지 않을까? 하는 생각이 들어요 
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
        {
            // If a fit is found, return the address the of block pointer
            return bp;
        }
    }
    return NULL; /* No fit */
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));

        /* next block PRED -> cur PRED 이식 */
        PUT_ADDRESS(PRED_LOC(NEXT_BLKP(bp)), PRED(bp));
        /* next block PRED -> cur PRED 이식 */
        PUT_ADDRESS(SUCC_LOC(NEXT_BLKP(bp)), SUCC(bp));

        bp = NEXT_BLKP(bp);

        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    }
    else
    {
        /* PRED block SUCC -> cur SUCC */
        PUT_ADDRESS(SUCC_LOC(PRED(bp)), SUCC(bp));
        /* PRED block PRED -> cur PRED */
        PUT_ADDRESS(PRED_LOC(SUCC(bp)), PRED(bp));

        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}
