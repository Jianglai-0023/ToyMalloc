/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  Blocks are never coalesced or reused.  The size of
 * a block is found at the first aligned word before the block (we need
 * it for realloc).
 *
 * This code is correct and blazingly fast, but very bad usage-wise since
 * it never frees anything.
 */
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"

/* If you want debugging output, use the following macro.  When you hand
 * in, remove the #define DEBUG line. */
// #define DEBUG
#ifdef DEBUG
# define dbg_printf(...) printf(__VA_ARGS__)
#else
# define dbg_printf(...)
#endif


/* do not change the following! */
#ifdef DRIVER
/* create aliases for driver tests */
#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif /* def DRIVER */

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
#define WSIZE 4
#define CHUNKSIZE (1<<12)
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define SIZE_PTR(p)  ((size_t*)(((char*)(p)) - SIZE_T_SIZE))

/*read and write a word at address p */
#define PUT(p,val) ((*(unsigned int *)(p))=(unsigned int)(val))

#define GET(p) (*(unsigned int *)(p))

/*read or put a ptr at address p*/
#define PUTPTR(p,addr)((*(size_t *)(p)) = (size_t)(addr))

#define GETPTR(p) (*(size_t *)(p))
/*read the size and allocation at address p*/
#define GET_SIZE(p) (GET(p) & ~0x7)//size means 有效内存

#define GET_ALLOC(p) (GET(p) & 0x1)
/* #in link list# given block ptr bp for next block or previous block*/
#define NEXT_BLK(bp) (GETPTR((char *) (bp) + ALIGNMENT))

#define PREV_BLK(bp) (GETPTR((char *)(bp)))
/*pack a size and allocated bit into a word*/
#define PACK(size,alloc) ((size) | (alloc))
/*find head ptr and footer ptr*/
#define HDBP(bp) ((char *)(bp) - WSIZE)

#define FTBP(bp) ((char*)(bp) + GET_SIZE((HDBP(bp))))
/*find adjecent prev block and next block*/
#define PREV_ALLOC(bp) (GET_ALLOC(((char *)HDBP(bp)) - WSIZE))

#define NEXT_ALLOC(bp) (GET_ALLOC(((char *)FTBP(bp)) + WSIZE)) 

#define PREV_SIZE(bp) (GET_SIZE(((char *)HDBP(bp)) - WSIZE))

#define NEXT_SIZE(bp) (GET_SIZE(((char *)FTBP(bp)) + WSIZE))

static char * heap_listp;
/*
* add_free_block - add free block to link list's head
*/
static void add_free_block(void *bp){
  dbg_printf("[add free block]\n");
  size_t next_block = GETPTR((char *)heap_listp + ALIGNMENT);
  PUTPTR(bp,heap_listp);
  PUTPTR(((char *)bp + ALIGNMENT),next_block);
//   // dbg_printf("WHAT\n");
//   // printf("%llx\n",next_block);
//   // printf("%llx\n",heap_listp);
// dbg_printf("(2)()\n");
  PUTPTR(next_block,bp);
  // dbg_printf("()()\n");
  PUTPTR(((char *)heap_listp + ALIGNMENT),bp);
  // dbg_printf("()(3)\n");
}
/*
* remove_free_block - remove free block in link list
*/
static void remove_free_block(void *bp){
  size_t prev_block = GETPTR(bp);
  size_t next_block = GETPTR((char *) bp + ALIGNMENT);
  PUTPTR(((char *)prev_block + ALIGNMENT),next_block);
  PUTPTR((char *)next_block, prev_block);
}
/*
* updateHF - update block's head and foot
*/
static void updateHF(void *bp, unsigned int size, size_t alloc){
  dbg_printf("[updateHF enter]\n");
  PUT(HDBP(bp),PACK(size,alloc));
  PUT(FTBP(bp),PACK(size,alloc));
}
/*
* coalesce - combine free blocks
*/
static int coalesce(void *bp){
  //todo 处理指针
    // dbg_printf("01\n");
    
    size_t pre_alloc = PREV_ALLOC(bp);
    size_t next_alloc = NEXT_ALLOC(bp);
    // dbg_printf("%llx\n",pre_alloc);
    // dbg_printf("%llx\n",next_alloc); 
    size_t size = GET_SIZE(HDBP(bp));
    char * next_block = (char *)bp + size + ALIGNMENT;
    char * prev_block = (char *)bp - ALIGNMENT - PREV_SIZE(bp);
    // dbg_printf("%d\n",PREV_SIZE(bp));
    if(pre_alloc && next_alloc)return 1;
    else if(pre_alloc && !next_alloc){//combine with next block
    // dbg_printf("02\n");
      size += NEXT_SIZE(bp) + 8;
      PUT((HDBP(bp)),PACK(size,0));
      PUT(FTBP(next_block),PACK(size,0));
      /*link list*/
      remove_free_block(next_block);
      add_free_block(bp);
    }else if(!pre_alloc && next_alloc){//combine with previous block
      // dbg_printf("[combine prev]\n");
      // dbg_printf("%lld\n",size);
      
      size += PREV_SIZE(bp) + 8;
      // dbg_printf("%lld\n",size);
      PUT(FTBP(bp),PACK(size,0));
      PUT(HDBP(prev_block),PACK(size,0));
      // dbg_printf("%llx\n",HDBP(prev_block));
      // mm_checkheap();
    }else{//combine with previous and next block
      size += PREV_SIZE(bp) + NEXT_SIZE(bp) + 16;
      PUT(FTBP(next_block),PACK(size,0));
      PUT(HDBP(prev_block),PACK(size,0)); 
      /*link list*/
      remove_free_block(next_block);
      remove_free_block(prev_block);
      add_free_block(prev_block);
    } 
    return 0;
}
/*
* extend_heap - use a new free block to extend the heap
*/
static void *extend_heap(size_t bytes){
    dbg_printf("[extend heap]\n");
    char * bp;
    size_t size;
    size = ALIGN(bytes);
    /*enough for ptrs*/
    if(size < 16)size = 16;
    /*add footer and header*/    
    if((size_t)(bp=mem_sbrk(size+8))==(size_t)-1)return NULL;
    /*initialize the new block's head and foot*/
    updateHF(bp,size,1);
    /*rewrite the tail head*/
    PUT((char*)FTBP(bp) + WSIZE,PACK(0,1));
    // dbg_printf("###\n");
    // printf("%llx\n",GETPTR((char *)heap_listp + ALIGNMENT));
    // printf("%llx\n",heap_listp);
    // add_free_block(bp);
    // dbg_printf("@@@@\n");
    return bp;
}
/*
* place - put words in a free block
*/
void place(void * bp, size_t size){
  dbg_printf("[place]\n");
  size_t bsize = GET_SIZE(HDBP(bp));
  //判断是否可以分割
  if(bsize - size > 32){
    // dbg_printf("[cut]\n");
    char * new_block = (char *)bp + size + ALIGNMENT;
    PUT(FTBP(bp),PACK(bsize-size - ALIGNMENT,0));
    PUT(HDBP(bp),PACK(size,1));
    PUT(((char *)bp + size), PACK(size,1));
    //put next head
    PUT((HDBP(new_block)),PACK(bsize-size - ALIGNMENT,0));
    remove_free_block(bp);
    add_free_block(new_block);
  }else{
    // dbg_printf("[notcut]\n");
    remove_free_block(bp);
    updateHF(bp,bsize,1);
  }
}
/*
* find_fit - to find a suitable block in the link list
*/
static char * find_fit(size_t size){
  // dbg_printf("[find_fit]\n");
  // printf("%llx\n",GETPTR((char *)heap_listp + ALIGNMENT));
  /*no free block right now*/
  if((char *)NEXT_BLK(heap_listp)==heap_listp){
    // printf("%llx\n",GETPTR((char *)heap_listp + ALIGNMENT)); 
    return extend_heap(size);
  }
  
  // printf("%llx\n",NEXT_BLK(heap_listp));
  // printf("%llx\n",heap_listp);
  char * bp = (char *)NEXT_BLK(heap_listp);

  // dbg_printf("%d\n",size);
  // dbg_printf("%llx\n",NEXT_BLK(heap_listp));
  // dbg_printf("%d\n",GET_SIZE(HDBP(bp))); 
  while(GET_SIZE(HDBP(bp)) < size && bp!=heap_listp){
    bp = (char *)NEXT_BLK(bp);
  }
  // dbg_printf("[find_fit]3\n");
  // dbg_printf("%llx\n",bp); 
  if(bp!=heap_listp){
    place(bp,size);
    return bp;
  }
  else return extend_heap(size);
}
/*
 * mm_init - Called when a new trace starts.
 */

int mm_init(void)
{
  dbg_printf("[mm_init] enter \n");
  /*create the initial empty block with header + prev + nxt + footer*/
  heap_listp = mem_sbrk(4*WSIZE + 2*ALIGNMENT);
  if(heap_listp == (void*)-1)return -1;
  PUT(heap_listp,0);//alignment padding
  PUT(((char*)heap_listp + (1*WSIZE)), PACK(2*ALIGNMENT,1)); // header
  PUTPTR(((char *)heap_listp + (2*WSIZE)),0); // prev
  PUTPTR(((char *)heap_listp + (2*WSIZE + ALIGNMENT)),(char*)heap_listp + 2*WSIZE); // nxt
  PUT(((char*)heap_listp + (2*WSIZE + 2*ALIGNMENT)), PACK(2*ALIGNMENT,1)); //footer
  PUT(((char *)heap_listp + 3*ALIGNMENT + WSIZE),PACK(0,1)); // tail head
  heap_listp += 2*WSIZE;
  // printf("%llx\n",GETPTR((char*)heap_listp + ALIGNMENT));
  // printf("%llx\n",heap_listp);
  /*extend the heap with empty block*/
  /*maybe it isn't good*/
  // if(extend_heap(CHUNKSIZE/WSIZE,heap_listp)==NULL)return -1;

  return 0;
}

/*
 * malloc - Allocate a block by incrementing the brk pointer.
 *      Always allocate a block whose size is a multiple of the alignment.
 */
void *malloc(size_t size)
{
  dbg_printf("[alloc]");
  dbg_printf("%d\n",size);
  // mm_checkheap();
  if(size == 0)return NULL;
  size_t asize = ALIGN(size);
  if(asize < 16) asize = 16;
  return find_fit(asize);
}

/*
 * free - We don't know how to free a block.  So we ignore this call.
 *      Computers have big memories; surely it won't be a problem.
 */
static int debugfree = 0;
void free(void *ptr){
  debugfree ++;
  dbg_printf("[free]");
  
	if(ptr==NULL)return;
  dbg_printf("%lld\n",GET_SIZE(HDBP(ptr)));
  if(GET_ALLOC(HDBP(ptr))==0)return;
  // dbg_printf("qwq");
  /*change alloc*/
  // dbg_printf("[updateHF]\n");
  updateHF(ptr,GET_SIZE(HDBP(ptr)),0);
  // dbg_printf("%lld\n",GET_SIZE(HDBP(ptr)));
  /*combine*/
  // dbg_printf("[combine]\n");
  int flag = coalesce(ptr);
  /*linked list*/
  // dbg_printf("[addfree]\n");
  // dbg_printf("%d\n",flag);
  if(flag)add_free_block(ptr);
//  dbg_printf("%lld\n",GET_SIZE(HDBP(ptr))); 
}

/*
 * realloc - Change the size of the block by mallocing a new block,
 *      copying its data, and freeing the old block.  I'm too lazy
 *      to do better.
 */
static int debug = 0;
void *realloc(void *oldptr, size_t size)
{
  debug ++;
  dbg_printf("[realloc]");
  dbg_printf("%lld\n",size);
  mm_checkheap();
  size_t oldsize;
  void *newptr;

  /* If size == 0 then this is just free, and we return NULL. */
  if(size == 0) {
    free(oldptr);
    mm_checkheap(); 
    return 0;
  }

  /* If oldptr is NULL, then this is just malloc. */
  if(oldptr == NULL) {
    return malloc(size);
  }

  newptr = malloc(size);

  /* If realloc() fails the original block is left untouched  */
  if(!newptr) {
    return 0;
  }

  /* Copy the old data. */
  oldsize = *SIZE_PTR(oldptr);
  if(size < oldsize) oldsize = size;
  memcpy(newptr, oldptr, oldsize);

  /* Free the old block. */
  free(oldptr);
  mm_checkheap();
  return newptr;
}
//
/*
 * calloc - Allocate the block and set it to zero.
 */
void *calloc (size_t nmemb, size_t size)
{
  size_t bytes = nmemb * size;
  void *newptr;

  newptr = malloc(bytes);
  memset(newptr, 0, bytes);

  return newptr;
}

/*
 * mm_checkheap - There are no bugs in my code, so I don't need to check,
 *      so nah!
 */
void mm_checkheap(int verbose){
	/*Get gcc to be quiet. */
	char *p = heap_listp;
  dbg_printf("[CHECK]\n");
  while(NEXT_BLK(p) != heap_listp){
    p = NEXT_BLK(p);
    dbg_printf("-----\n");
    dbg_printf("%llx %lld\n",HDBP(p),GET_SIZE(HDBP(p)));
    dbg_printf("******\n"); 
  }
}
