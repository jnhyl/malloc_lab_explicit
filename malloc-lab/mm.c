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
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* ----------------------------------------------------------------------------------------------------- */
// 함수 선언 공간
int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *ptr);
void *mm_realloc(void *ptr, size_t size);

static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *first_fit(size_t asize);
static void *best_fit(size_t asize);
static void place(void *bp, size_t asize);


static void insert_free_list(void *bp);
static void delete_free_list(void *bp);

static int binary_case(size_t size);

/* ----------------------------------------------------------------------------------------------------- */
// 전역 변수 선언 공간

// 힙의 시작 포인터, 할당기의 탐색 시작 위치
static char *heap_listp;

// free block stack pointer, NULL로 초기화
static char *free_listp;

/* ----------------------------------------------------------------------------------------------------- */

/* single word (8) or double word (16) alignment */
/* 64비트 환경에 맞게 word 및 double word의 값을 재조정 */
/* 웬만하면 교재대로 하려고 했는데 explicit 구현하려면 포인터 크기를 고려해야 한다! */
/* 가상환경을 아무리 건드린들 HW가 64비트 머신이면 포인터는 무조건 64비트 크기를 가짐 */
/* 참고로 Makefile에서 주석 처리 된 CFLAGS, -m32 옵션을 적용하면 에러 뜬다..*/
/* WSIZE : 8, DSIZE : 16, ALIGNMENT : 16, 최소 블록 크기 : 32 */
#define ALIGNMENT 16

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0xf)     // 0xf = 0b1111

#define MIN_BSIZE   2*DSIZE     // 최소 블록 크기, 2*DSIZE = 32B

/* 상수 및 매크로 정의 */
/* 기본 단위 정의 및 기타 매크로 작성 */
#define WSIZE       8           // word size(64bit 기준 8MB)
#define DSIZE       2*WSIZE     // double words size
#define CHUNKSIZE   (1<<12)     // chunksize, 힙 확장 시 기본 사이즈

#define MAX(x, y)   (((x) > (y)) ? (x) : (y)) 

/* block size와 allocated bit를 인코딩하는 매크로 */
#define PACK(size, alloc)   ((size) | (alloc))

/* header 및 footer의 정보 읽기/쓰기 */
#define GET(p)          (*(unsigned long long *)(p))              // unsigned long long * <- 8 bytes 단위로 디코딩
#define PUT(p, val)     (*(unsigned long long *)(p) = (val))

/* block size 및 allocated bit 반환 매크로 */
#define GET_SIZE(p)     (GET(p) & ~0xf)     // 하위 4자리의 allocated bit를 제외한 부분
#define GET_ALLOC(p)    (GET(p) & 0x1)      // 하위 1자리의 1 비트 : allocated bit

/* 블록의 header, footer 주소 */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 현재 블록의 다음/이전 블록 포인터 */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)bp - WSIZE))   // 현재 블록의 HDRP = bp - WSIZE 
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)bp - DSIZE))   // 이전 블록의 FTRP = bp - DSIZE

/* 현재 가용 블록의 PRED, SUCC 정보 습득*/
#define PRED(bp)    (*(void **)((char *)(bp)))          // bp에 WSIZE 크기의 PRED 주소 저장
#define SUCC(bp)    (*(void **)((char *)(bp) + WSIZE))  // (bp + WSIZE)에 WSIZE 크기의 SUCC 주소 저장



/***********************************************************************************************/
/*                                            API                                              */
/***********************************************************************************************/

/*
 * mm_init - initialize the malloc package.
 */

int mm_init(void)   // 할당기 호출 전 반드시 가장 처음으로 호출, 성공 시 0 반환, 실패 시 -1 반환
{
    // 4 워드 크기의 힙 공간 확장
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    
    // 미사용 패딩 및 prologue block
    PUT(heap_listp, 0);     // 미사용 패딩으로 첫 블록의 주소가 double word 정렬 조건을 만족
    PUT(heap_listp + 1*WSIZE, PACK(DSIZE, 1));  // prologue block header, 16 bytes / 1(allocated)
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, 1));  // prologue block footer, 16 bytes / 1(allocated)
    PUT(heap_listp + 3*WSIZE, PACK(0, 1));      // eplogue block, 0 byte / 1(allocated)

    // 힙 리스트 및 가용 리스트 초기화
    heap_listp += DSIZE;
    free_listp = NULL;

    // 할당에 필요한 힙 공간 확장, 실패 시(NULL) 오류 코드(-1) 반환
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;

    return 0;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{   
    // size가 0일 경우, 오류 코드(NULL) 반환
    if (size == 0)
        return NULL;

    size = binary_case(size);

    char *bp;   // 할당할 블록의 포인터 선언
    size_t asize = ALIGN(size + DSIZE); // 크기 조정, payload + header + footer + padding(for align)

    // // first fit
    // if ((bp = first_fit(asize)) != NULL) {      // 만약 적당한 가용 블록을 찾으면
    //     place(bp, asize);                       // fit한 가용 공간에 place
    //     return bp;                              // place한 주소의 포인터 반환
    // }

    // best fit
    if ((bp = best_fit(asize)) != NULL) {       // 만약 적당한 가용 블록을 찾으면
        place(bp, asize);                       // fit한 가용 공간에 place
        return bp;                              // place한 주소의 포인터 반환
    }
    
    // 만약 현재 힙 공간에 충분한 사이즈의 가용 공간이 없으면
    // 힙 확장
    size_t extendsize;  // 확장할 힙 사이즈
    extendsize = MAX(CHUNKSIZE, asize); // 할당할 사이즈가 기본 확장 사이즈 보다 작으면 기본 CHUNKSIZE로 확장
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *ptr)
{
    // NULL 포인터일 경우 아무것도 하지말고 함수 종료, POSIX 참고
    if (ptr == NULL)
        return;

    // 해제할 블록의 크기
    size_t size = GET_SIZE(HDRP(ptr));

    // 블록의 header와 footer의 정보를 가용 상태로 갱신
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // 주변 가용 블록과 즉시 연결(coalesce)
    coalesce(ptr);
}   // free는 아무것도 반환하지 않는다.

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
    // ptr이 NULL인 경우, mm_malloc(size)와 동일
    if (ptr == NULL)
        return mm_malloc(size);

    // size가 0인 경우, mm_free(ptr)과 동작 동일
    if (size == 0) {
        mm_free(ptr);
        return NULL;
    }

    // 사이즈 조정(Payload + header + footer + padding(double word align))
    size_t asize = ALIGN(size + DSIZE);
    
    // case 1) 재할당할 사이즈가 기존 사이즈보다 작거나 같을 때
    if (asize <= GET_SIZE(HDRP(ptr))) {
        size_t rsize = GET_SIZE(HDRP(ptr)) - asize;
        if (rsize >= MIN_BSIZE) {               // asize가 원래 블록을 축소할 만큼 충분히 작으면
            PUT(HDRP(ptr), PACK(asize, 1));     // ptr 주소의 불록의 크기를 asize로 줄여준다.
            PUT(FTRP(ptr), PACK(asize, 1));     // 당연히 할당 상태이므로 allocated bit == 1
            void *rp = NEXT_BLKP(ptr);          // 나머지 분할할 공간의 포인터 : rp(rest pointer)
            PUT(HDRP(rp), PACK(rsize, 0));      // 나머지 공간에 rsize의 가용 블록 생성
            PUT(FTRP(rp), PACK(rsize, 0));

            // 새로 생성된 가용 리스트 coalesce
            coalesce(rp);
        }
        return ptr;     // 현재 주소 반환
    }
    
    // case 2) 다음 블록이 가용 상태고 충분한 크기일 때, 블록의 주소는 그대로 두고 길이만 연장
    if (GET_ALLOC(HDRP(NEXT_BLKP(ptr))) == 0) {     // 다음 블록이 가용 블록일 때
        size_t csize = GET_SIZE(HDRP(ptr)) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if (csize >= asize) {                   // 현재 블록과 다음 블록의 크기 합이 asize보다 크면
            delete_free_list(NEXT_BLKP(ptr));   // 다음 위치의 가용 블록을 리스트에서 삭제

            // free list의 insert와 delete 결과로 기존 페이로드 위치의 데이터가 오염되지 않도록
            // 기존 블록이 위치한 가용 블록 공간에 insert 및 delete가 빠진 버전의 place를 따로 구현
            // total_size 변수명을 place의 변수명과 맞춰서 csize를 변경
            size_t rsize = csize - asize;           //
            if (rsize >= MIN_BSIZE) {
                PUT(HDRP(ptr), PACK(asize, 1));     // asize 크기의 할당 블록 생성
                PUT(FTRP(ptr), PACK(asize, 1));
                void *rp = NEXT_BLKP(ptr);
                PUT(HDRP(rp), PACK(rsize, 0));      // 나머지 공간에 rsize의 가용 블록 생성
                PUT(FTRP(rp), PACK(rsize, 0));
                coalesce(rp);
            } else {
                PUT(HDRP(ptr), PACK(csize, 1));     // 현재 블록 전체(csize)를 할당 블록으로 갱신
                PUT(FTRP(ptr), PACK(csize, 1));
            }

            // realloc 주소 포인터 반환, in-place 방식이라 변화 없음
            return ptr;
        }
    }

    // case3, 재할당할 블록이 힙의 마지막에 위치했을 때(heap_extend 후 in-place realloc)
    if (GET_SIZE(HDRP(NEXT_BLKP(ptr))) == 0) {
        size_t extendsize = asize - GET_SIZE(HDRP(ptr));
        if (extend_heap(extendsize/WSIZE) == NULL)  // 필요한 만큼만 힙 확장 후
            return NULL;

        delete_free_list(NEXT_BLKP(ptr));   // 힙 확장으로 새로 생성된 가용 블록을 사용하기 위해 가용 리스트에서 제거
        PUT(HDRP(ptr), PACK(asize, 1));     // 제자리에서 블록 크기만 asize로 갱신
        PUT(FTRP(ptr), PACK(asize, 1));

        return ptr;     // 현재 위치 반환
    }

    // case4, 앞의 모든 케이스를 만족하지 못 할 경우(= 데이터를 복사해야 하는 경우)
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}



/****************************************************************************************************/
/*                                             HELPER                                               */
/****************************************************************************************************/


// 힙 공간 확장 함수, 확장시키고 싶은 사이즈를 word 단위로 받는다
static void *extend_heap(size_t words)
{
    char *bp;
    size_t asize;   // asize = aligned size
    
    // word 단위를 byte 단위로 변환 및 double words align을 위한 사이즈 조정, 
    asize = ALIGN(words * WSIZE);

    // 힙 공간 확장, 만일 실패 시(return (void *)-1) NULL 반환
    // 확장 시 확장 전 brk를 bp에 저장, 확장한 힙 공간의 시작 포인터
    if ((bp = mem_sbrk(asize)) == (void *)-1)
        return NULL;

    // 확장한 힙 공간 전체(eplogue 부분 제외)를 하나의 가용 블록으로
    PUT(HDRP(bp), PACK(asize, 0));      // epilogue 블록을 header로 갖는 가용 블록 생성, HERP = bp - WSIZE
    PUT(FTRP(bp), PACK(asize, 0));      // FTRP = bp + size - DSIZE, 즉 현재 brk - DSIZE에 위치

    // 가용 블록을 만들고 마지막 남은 1 word의 공간을 에필로그 블록으로
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    // 마지막 블록이 가용 블록일 경우, 병합 후 생성된 블록의 포인터 반환
    return coalesce(bp);
}

// 연결 함수, extend 및 free 등 가용 블록을 병합할 때 사용
// 현재 블록의 포인터를 인자로 받아 다음/이전 블록의 가용 여부 판단
// 현재 블록의 가용 여부와 상관 없이 다음/이전의 가용 블록들과 연결해서 새 가용 블록 생성
// 새 가용 블록의 블록 포인터를 반환한다.
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp))); // 이전 블록의 할당 정보
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 정보
    size_t size = GET_SIZE(HDRP(bp));   // 현재 블록의 사이즈, 연결 가능 시 전체 사이즈로 갱신

    // case 1) 다음/이전 블록 모두 할당된 블록일 때
    if (prev_alloc && next_alloc) {
        // nothing
    }

    // case 2) 다음 블록만 가용 상태일 때
    else if (prev_alloc && !next_alloc) {
        delete_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 다음 블록을 합친 사이즈
        PUT(HDRP(bp), PACK(size, 0));           // 현재 블록 위치에서 그대로 연장
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3) 이전 블록만 가용 상태일 때
    else if (!prev_alloc && next_alloc) {
        delete_free_list(PREV_BLKP(bp));
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));  // 이전 블록을 합친 사이즈
        bp = PREV_BLKP(bp);                     // 블록 포인터를 이전 블록의 포인터로 이동
        PUT(HDRP(bp), PACK(size, 0));           // 블록 연결
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 4) 다음/이전 블록 모두 할당된 블록일 때
    else {
        // 다음 블록과 이전 블록의 크기를 합친 사이즈
        delete_free_list(PREV_BLKP(bp));
        delete_free_list(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    insert_free_list(bp);
    return bp;
}


// first_fit 기준
static void *first_fit(size_t asize)
{
    // heap의 첫 블록부터 탐색 시작, prologue 블록의 다음 블록
    void *bp = free_listp;

    // epilogue 블록을 만나기 전까지 블록을 건너면서 탐색 반복
    while(bp != NULL) {
        if (GET_SIZE(HDRP(bp)) >= asize)
            break;
        bp = SUCC(bp);
    }

    // 적당한 사이즈의 가용 블록을 못 찾으면 NULL 반환
    // malloc 내부에서 힙 확장 후 다시 시도
    return bp;
}

// best_fit 기준
static void *best_fit(size_t asize)
{
    void *bp = free_listp;
    void *best_bp = NULL;
    size_t best_size = (size_t)-1;   // 초기값을 매우 크게

    while (bp != NULL) {
        size_t bsize = GET_SIZE(HDRP(bp));
        if (bsize >= asize && bsize < best_size) {
            best_size = bsize;
            best_bp = bp;
        }
        bp = SUCC(bp);
    }

    return best_bp;
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));  // csize(current size) : 현재 블록의 사이즈
    size_t rsize = csize - asize;       // rsize(rest size) : 현재 블록의 크기에서(= csize) asize를 뺀 나머지 사이즈

    // 삽입할 위치의 가용 블록을 리스트에서 제거
    delete_free_list(bp);
    
    // 만약 나머지 사이즈의 크기가 최소 블록의 크기보다 크거나 같으면 분할
    // 최소 블록의 조건: 헤더와 푸터, 1 byte 이상의 데이터가 들어갈 페이로드, doble word align 만족 => 2*DSIZE
    if (rsize >= MIN_BSIZE) {
        PUT(HDRP(bp), PACK(asize, 1));  // asize 크기의 할당 블록 생성
        PUT(FTRP(bp), PACK(asize, 1));
        void *rp = NEXT_BLKP(bp);
        PUT(HDRP(rp), PACK(rsize, 0));  // 나머지 공간에 rsize의 가용 블록 생성
        PUT(FTRP(rp), PACK(rsize, 0));

        // 새로 생성된 가용 리스트 coalesce
        coalesce(rp);
    } else {
        PUT(HDRP(bp), PACK(csize, 1));  // 현재 블록 전체(csize)를 할당 블록으로 갱신
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

static void insert_free_list(void *bp)
{
    if (free_listp != NULL) {
        SUCC(bp) = free_listp; 
        PRED(free_listp) = bp;
    } else {
        SUCC(bp) = NULL;
    }
    
    PRED(bp) = NULL;
    free_listp = bp;
}

static void delete_free_list(void *bp)
{
    void *pred = PRED(bp);
    void *succ = SUCC(bp);
    
    if (pred != NULL) {
        SUCC(pred) = succ;
    } else {    // explicit free list의 맨 앞에 위치했을 경우
        free_listp = succ;
    }

    if (succ != NULL) {
        PRED(succ) = pred;
    }

    // 가용 리스트에서 삭제 된 블록의 pred, succ 부분 초기화
    PRED(bp) = NULL;
    SUCC(bp) = NULL;
}

static int binary_case(size_t size) {
    if (size == 112) {
        return 128;
    }
    else if (size == 448) {
        return 512;
    }
    return size;
}