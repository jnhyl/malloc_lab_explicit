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

/* ----------------------------------------------------------------------------------------------------- */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 상수 및 매크로 정의 */
/* 기본 단위 정의 및 기타 매크로 작성 */
#define WSIZE       4       // word size
#define DSIZE       8       // double words size
#define CHUNKSIZE   (1<12)  // chunksize, 힙 확장 시 기본 사이즈

#define MAX(x, y)   (((x) > (y)) ? (x) : (y)) 

/* block size와 allocated bit를 인코딩하는 매크로 */
#define PACK(size, alloc)   ((size) | (alloc))

/* header 및 footer의 정보 읽기/쓰기 */
#define GET(p)          (*(unsigned int *)(p))
#define PUT(p, val)     (*(unsigned int *)(p) = (val))

/* block size 및 allocated bit 반환 매크로 */
#define GET_SIZE(p)     (GET(p) & ~0x7)     // 하위 3자리의 allocated bit를 제외한 부분
#define GET_ALLOC(p)    (GET(p) & 0x1)      // 하위 1자리의 1 비트 : allocated bit

/* 블록의 header, footer 주소 */
#define HDRP(bp)        ((char *)(bp) - WSIZE)
#define FTRP(bp)        ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* 현재 블록의 다음/이전 블록 포인터 */
#define NEXT_BLKP(bp)   ((char *)(bp) + GET_SIZE((char *)bp - WSIZE))   // 현재 블록의 HDRP = bp - WSIZE 
#define PREV_BLKP(bp)   ((char *)(bp) - GET_SIZE((char *)bp - DSIZE))   // 이전 블록의 FTRP = bp - DSIZE

/*
 * mm_init - initialize the malloc package.
 */

// 힙의 시작 포인터, 할당기의 탐색 시작 위치
static char *heap_listp;

int mm_init(void)   // 할당기 호출 전 반드시 가장 처음으로 호출, 성공 시 0 반환, 실패 시 -1 반환
{
    // 4 워드 크기의 힙 공간 확장(padding(1 word) + prologue block(2 words) + epilogue(1 word))
    // sbrk 함수로 함수 확장 후 만약 실패 시(return (void *)-1) 오류 코드(-1) 반환
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    
    // +) 미사용 패딩 덕분에 첫 블록의 주소(= payload의 주소)는 8의 배수, double word 정렬 조건을 만족
    PUT(heap_listp, 0); // 더블 워드 경계로 정렬된 미사용 패딩 워드
    PUT(heap_listp + 1*WSIZE, PACK(DSIZE, 1));  // prologue block header, 8 bytes / 1(allocated)
    PUT(heap_listp + 2*WSIZE, PACK(DSIZE, 1));  // prologue block footer, 8 bytes / 1(allocated)
    PUT(heap_listp + 3*WSIZE, PACK(0, 1));      // eplogue block, 0 byte / 1(allocated)

    heap_listp += 2*WSIZE;  // prologue block을 힙의 시작 위치로, 이로써 double word align 성립

    // 할당에 필요한 힙 공간 확장, 실패 시(NULL) 오류 코드(-1) 반환
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

// 힙 공간 확장 함수, 확장시키고 싶은 사이즈를 word 단위로 받는다
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    
    // double words align을 위한 사이즈 조정, word 단위를 byte 단위로 변환
    size = ALIGN(words * WSIZE);

    // 힙 공간 확장, 만일 실패 시(return (void *)-1) NULL 반환
    // 확장 시 확장 전 brk를 bp에 저장, 확장한 힙 공간의 시작 포인터
    if ((long *)(bp = mem_sbrk(size)) == (void *)-1)
        return NULL;

    // 확장한 힙 공간 전체(eplogue 부분 제외)를 하나의 가용 블록으로
    PUT(HDRP(bp), PACK(size, 0));   // epilogue 블록을 header로 갖는 가용 블록 생성, HERP = bp - WSIZE
    PUT(FTRP(bp), PACK(size, 0));   // FTRP = bp + size - DSIZE, 즉 현재 brk - DSIZE에 위치

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
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 할당 정보
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 할당 정보
    size_t size = GET_SIZE(HDRP(bp));   // 현재 블록의 사이즈, 연결 가능 시 전체 사이즈로 갱신

    // case 1) 다음/이전 블록 모두 할당된 블록일 때
    if (prev_alloc && next_alloc) {
        return bp;
    }

    // case 2) 다음 블록만 가용 상태일 때
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));  // 다음 블록을 합친 사이즈
        PUT(HDRP(bp), PACK(size, 0));           // 현재 블록 위치에서 그대로 연장
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 3) 이전 블록만 가용 상태일 때
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(FTRP(PREV_BLKP(bp)));  // 이전 블록을 합친 사이즈
        bp = PREV_BLKP(bp);                     // 블록 포인터를 이전 블록의 포인터로 이동
        PUT(HDRP(bp), PACK(size, 0));           // 블록 연결
        PUT(FTRP(bp), PACK(size, 0));
    }

    // case 4) 다음/이전 블록 모두 할당된 블록일 때
    else {
        // 다음 블록과 이전 블록의 크기를 합친 사이즈
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))) + GET_SIZE(FTRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    return bp;
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
        return NULL;
    else
    {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
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
    void *oldptr = ptr;
    void *newptr;
    size_t copySize;

    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
        copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;
}