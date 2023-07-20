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
 * provide your information in the following struct.
 ********************************************************/
team_t team = {
    /* Your student ID */
    "20160169",
    /* Your full name*/
    "Seonghwan Park",
    /* Your email address */
    "empodi31@gmail.com",
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT               8
#define WSIZE                   4           /* Word and header/footer size (bytes) */
#define DSIZE                   8           /* Double word size (bytes) */
#define CHUNKSIZE               (1<<8)      /* Extend heap by this amount (bytes) */
#define SEG_LIST_NUM            20          /* Number of entries in segregated list */

#define MAX(x,y)                ((x) > (y) ? (x) : (y))

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size)             (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE             (ALIGN(sizeof(size_t)))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)       ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)                  (*(unsigned int *)(p))  // returns the word reference by p
#define PUT(p, val)             (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
/* From header and footer!! */
#define GET_SIZE(p)             (GET(p) & ~07)
#define GET_ALLOC(p)            (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)                ((char *)(bp) - WSIZE)
#define FTRP(bp)                ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

#define FREE_HEADER(bp, size)   (PUT(HDRP(bp), PACK(size,0)))
#define FREE_FOOTER(bp, size)   (PUT(FTRP(bp), PACK(size,0)))
#define SET_HEADER(bp, size)    (PUT(HDRP(bp), PACK(size,1)))
#define SET_FOOTER(bp, size)    (PUT(FTRP(bp), PACK(size,1))) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)           ((char *)(bp) + GET_SIZE(((char *)(bp)- WSIZE)))
#define PREV_BLKP(bp)           ((char *)(bp) - GET_SIZE(((char *)(bp)- DSIZE)))

#define SEG_FIND(p, idx)        *((char **)p + idx)
#define SEG_INIT_NULL(p, idx)   (SEG_FIND(p, idx) = NULL)
#define NEXT_SEG(bp)            *((char **)bp + 1)
#define PREV_SEG(bp)            *((char **)bp)
#define SEG_NEXT_OF_PREV(bp)    (NEXT_SEG(PREV_SEG(bp)))
#define SEG_PREV_OF_NEXT(bp)    (PREV_SEG(NEXT_SEG(bp)))

/* heap_listp always points to the prologue block: 8 byte allocated block consisting of only a header and a footer */
static char *heap_listp = NULL;
static char *seg_listp = NULL;

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t aszie);
static void insert_free_block(void *bp);
static void remove_free_block(void *bp);
static unsigned int find_seg_idx(size_t asize);

typedef int block_action_func(void *seg_p);
static int mm_check();
static int traverse(block_action_func *func);
static int check_blocks_in_heap(void *seg_p);
static int check_free_blocks_in_seg();
static int check_free_block_mark(void *seg_p);
static int check_coalesce (void *seg_p);

/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) { 

    int i;
    if ((seg_listp = mem_sbrk(SEG_LIST_NUM * WSIZE)) == (void *) - 1){
        return -1;
    }
    for (i = 0; i < SEG_LIST_NUM; i++){
        SEG_INIT_NULL(seg_listp, i);
    }

    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *) - 1) {
        return -1;
    }

    PUT(heap_listp, 0);                             /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1));    /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));    /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));        /* Epilogue header */
    heap_listp += (2*WSIZE);

    /* Extend the empty heap by CHUNKSIZE bytes and creates the initial free block */
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL) {
        return -1;
    }
    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {  

    size_t asize;           /* Adjusted block size */
    size_t extendsize;      /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment requests. */
    if (size <= DSIZE) {
        // enforce the minimum block size of 16 bytes
        // 8 bytes for alignment and 8 bytes for the header and footer
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
    }

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);   // split
        return bp;
    }

    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) {
        return NULL;
    }
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block.
 */
void mm_free(void *bp){ 

    size_t size = GET_SIZE(HDRP(bp));

    FREE_HEADER(bp, size);
    FREE_FOOTER(bp, size);

    bp = coalesce(bp);
    insert_free_block(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size) { 
    
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;

    copySize = GET_SIZE(HDRP(oldptr));
    copySize = size < copySize ? size : copySize;

    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}

static void *extend_heap(size_t words) {   

    char *bp;
    size_t size;
    /*
        Allocate an even number of words to maintain alignment
        Rounds up the requested size to the nearest multiple of 2 words (8 bytes)
    */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1) {    // request the additional heap space from the memory
        return NULL;
    }

    /* Initialize free block header/footer and the epilogue header */
    FREE_HEADER(bp, size);                  /* Free block header */
    FREE_FOOTER(bp, size);                  /* Free block footer */
    SET_HEADER(NEXT_BLKP(bp), 0);           /* New epilogue header */

    /* Coalesce if the previous block was free */
    bp = coalesce(bp);
    insert_free_block(bp);
    return bp;
}

static void *coalesce(void *bp) {

    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && !next_alloc) {   
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        remove_free_block(NEXT_BLKP(bp));
        FREE_HEADER(bp, size);                  
        FREE_FOOTER(bp, size); 
    }

    else if (!prev_alloc && next_alloc) {   
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        remove_free_block(PREV_BLKP(bp));
        FREE_HEADER(PREV_BLKP(bp), size);
        FREE_FOOTER(bp, size);
        bp = PREV_BLKP(bp);
    }

    else if (!prev_alloc && !next_alloc) {                              
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        remove_free_block(PREV_BLKP(bp));
        remove_free_block(NEXT_BLKP(bp));
        FREE_HEADER(PREV_BLKP(bp), size);
        FREE_FOOTER(NEXT_BLKP(bp), size);
        bp = PREV_BLKP(bp);
    }

    return bp;  /* This include the case when prev and next are all allocated */
}

static void *find_fit(size_t asize) {   

    /* First-fit search */
    unsigned int idx = find_seg_idx(asize);

    while (idx < SEG_LIST_NUM) {
        void* bp = SEG_FIND(seg_listp, idx);
        while (bp) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
            bp = NEXT_SEG(bp);
        }
        idx++;
    }
    return NULL; /* NO fit */
}

static void place(void *bp, size_t asize) {

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2 * DSIZE)) {
        remove_free_block(bp);
        SET_HEADER(bp, asize);
        SET_FOOTER(bp, asize);
        bp = NEXT_BLKP(bp);
        FREE_HEADER(bp, csize - asize);
        FREE_FOOTER(bp, csize - asize);
        bp = coalesce(bp);
        insert_free_block(bp);
    }
    else {
        remove_free_block(bp);
        SET_HEADER(bp, csize);
        SET_FOOTER(bp, csize);
    }
}

static void insert_free_block(void *bp) {   

    size_t csize = GET_SIZE(HDRP(bp));
    unsigned int idx = find_seg_idx(csize);
    char** targ = &(SEG_FIND(seg_listp, idx));

    PREV_SEG(bp) = NEXT_SEG(bp) = NULL;

    if (*targ) {
        NEXT_SEG(bp) = *targ;
        PREV_SEG(*targ) = bp;
    }
    *targ = bp;
}

static void remove_free_block(void *bp) {   

    size_t csize = GET_SIZE(HDRP(bp));
    unsigned int idx = find_seg_idx(csize);

    if (bp == SEG_FIND(seg_listp, idx)) {
        SEG_FIND(seg_listp, idx) = NEXT_SEG(bp);
    }
    else if (PREV_SEG(bp) && NEXT_SEG(bp)) {
        SEG_NEXT_OF_PREV(bp) = NEXT_SEG(bp);
        SEG_PREV_OF_NEXT(bp) = PREV_SEG(bp);
    }
    else if (PREV_SEG(bp) && !NEXT_SEG(bp)) {
        SEG_NEXT_OF_PREV(bp) = NULL;
    }
    else if (NEXT_SEG(bp) && !PREV_SEG(bp)) {
        SEG_PREV_OF_NEXT(bp) = NULL;
    }
}

static unsigned int find_seg_idx(size_t asize) {

    size_t target_size = asize / DSIZE;
    int idx = 1;

    while (idx < SEG_LIST_NUM) {
        if (target_size < (1<<idx)) {
            return idx - 1;
        }
        idx++;
    }

    return idx - 1;
}

static int mm_check() {     // return 0 if error, else return 1

    int result = 1, tmp;

    /* Check if all free blocks are in valid heap */
    result = traverse(check_blocks_in_heap);
    
    /* Check if all free blocks are in segregated list */
    tmp = check_free_blocks_in_seg();
    if (result && !tmp) result = tmp;

    /* Check if all free blocks in segregated list are marked free */
    tmp = traverse(check_free_block_mark);
    if (result && !tmp) result = tmp;

    /* Check if coalesce working */
    tmp = traverse(check_coalesce);
    if (result && !tmp) result = tmp;
    
    return result;
}

static int check_free_blocks_in_seg() {

    int i;
    void *hp;

    for (hp = heap_listp; GET_SIZE(HDRP(hp)); hp = NEXT_BLKP(hp)) {
        if (!GET_ALLOC(HDRP(hp))) {
                
            int found = 0;
            for (i = 0; i < SEG_LIST_NUM && !found; i++) { 
                void* seg_p = SEG_FIND(seg_listp, i);
                while (seg_p) {
                    if (seg_p == hp) {
                        found = 1;
                        break;
                    }
                    seg_p = NEXT_SEG(seg_p);
                }
            }
            if (!found) {
                printf("%p: Error: free block but not in segregated list. \n", hp);
            }
            else {
                //printf("%p: FOUND \n", hp);
                return 1;
            }
        }
    }
    return 0;
}

static int traverse(block_action_func *func) {    // return 0 if error, else return 1
    int i, result = 1;

    for (i = 0; i < SEG_LIST_NUM; i++){ 
        void* seg_p = SEG_FIND(seg_listp, i);
        while (seg_p) {
            int val = func(seg_p);
            if (result && !val) result = val;
            
            seg_p = NEXT_SEG(seg_p);
        }
    }
    return result;
}

static int check_blocks_in_heap(void *seg_p) {
    if (seg_p < mem_heap_lo() || seg_p > mem_heap_hi()) {
        printf("%p: Error: free block not in valid heap address. \n", seg_p);
        return 0;
    }
    return 1;
}

static int check_free_block_mark(void *seg_p) {
    if (GET_ALLOC(HDRP(seg_p)) == 1) {
        printf("%p: Error: block in segregated list but not marked free. \n", seg_p);
        return 0;
    }
    return 1;
}

static int check_coalesce (void *seg_p) {
    void *prev = PREV_BLKP(seg_p);
    void *next = NEXT_BLKP(seg_p);
    if (prev && !GET_ALLOC(HDRP(prev))) {
        printf("%p, %p: Error: Contiguous free blocks but not coalesced. \n", prev, seg_p);
        return 0;
    }
    if (next && !GET_ALLOC(HDRP(next))) {
        printf("%p, %p: Error: Contiguous free blocks but not coalesced. \n", seg_p, next);
        return 0;
    }
    /*
    if (next)
        printf("%p: Coalescing done. Next_seg_alloc : %d \n", seg_p, GET_ALLOC(HDRP(next)));
    */
    return 1;
}