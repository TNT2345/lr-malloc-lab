//复刻textbook的极限就到这里了
//将大局逆转吧！显式空闲链表！！！
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "memlib.h"
#include "mm.h"
//桶数为NCLASS
#define NCLASS 16
//读取bp里面储存的一个指向前节点的指针
#define PREV_PTR(bp) (*(char **)(bp))
//读取bp里面储存的一个指向后节点的指针
#define NEXT_PTR(bp) (*(char **)((char *)(bp) + DSIZE))
//单字4字节
#define WSIZE 4
//双字8字节
#define DSIZE 8
//一次扩容的大小
#define CHUNKSIZE (1 << 12)
//扩容的最小块大小
#define MINBLOCK (3 * DSIZE)
//取最大值
#define MAX(x, y) ((x) > (y) ? (x) : (y))
//将size（大小）和alloc（是否被分配压入一起）
#define PACK(size, alloc) ((size) | (alloc))
//获取指针p内的数据
#define GET(p) (*(unsigned int *)(p))
//将指针p指向的数据内容设置为val
#define PUT(p, val) (*(unsigned int *)(p) = (val))
//获取header和footer内部的大小信息
#define GET_SIZE(p) (GET(p) & ~0x7)
//读取header和footer内部是否被分配的标志位
#define GET_ALLOC(p) (GET(p) & 0x1)
//获取传递给用户的bp对应的header位置
#define HDRP(bp) ((char *)(bp) - WSIZE)
//获取传递给用户的bp对应的footer位置
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)
//获取下一个bp的位置
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE((char *)(bp) - WSIZE))
//获取上一个bp的位置
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE((char *)(bp) - DSIZE))
//起点指针
static char *heap_listp = NULL;
//NCLASS个串
static char * free_list[NCLASS];

//mem_sbrk(incr):把堆增大incr字节，返回新区域的第一字节地址，失败返回 (void*)-1

//按照尺寸进行分组
static int size_class(size_t asize){
  int class_number = 0;
  for(; class_number < NCLASS - 1 && asize > 16; asize >>= 1){
    class_number++;
  }
  return class_number;
}

//给定
static void insert_free(void *bp, int class_number){
  PREV_PTR(bp) = NULL;//bp指针下一项是NULL
  NEXT_PTR(bp) = free_list[class_number];//bp指针上一项是原来的头指针
  if(free_list[class_number] != NULL){
    PREV_PTR(free_list[class_number]) = bp;//原来头指针的上一项是bp
  }
  free_list[class_number] = bp;
}

//接头霸王
static void remove_free(void *bp, int class_number){
  if(PREV_PTR(bp) != NULL){
    NEXT_PTR(PREV_PTR(bp)) = NEXT_PTR(bp);
  }
  else{
    free_list[class_number] = NEXT_PTR(bp);
    //更新头节点位置
  }
  if(NEXT_PTR(bp) != NULL){
    PREV_PTR(NEXT_PTR(bp)) = PREV_PTR(bp);
  }
}







//任务是合并前块和后块的空闲块，并且更新bp的位置
static void coalesce_helper(void * bp){
  size_t size = GET_SIZE(HDRP(bp)) + GET_SIZE(HDRP(NEXT_BLKP(bp)));//自己的大小，加上后面的大小
  PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
  PUT(HDRP(bp), PACK(size, 0));
}
static void *coalesce(void *bp){
  if(GET_ALLOC(HDRP(NEXT_BLKP(bp))) == 0){
    remove_free(NEXT_BLKP(bp), size_class(GET_SIZE(HDRP(NEXT_BLKP(bp)))));
    coalesce_helper(bp);
  }
  if(GET_ALLOC(bp - DSIZE) == 0){
    bp = PREV_BLKP(bp);
    remove_free(bp, size_class(GET_SIZE(HDRP(bp))));
    coalesce_helper(bp);
  }
  insert_free(bp, size_class(GET_SIZE(HDRP(bp))));
  return bp;
}

static void *extend_heap(size_t words){
  char *bp;
  size_t size;
  size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;//size调整为8倍数
  if ((bp = mem_sbrk((int)size)) == (void *)-1) return NULL;
  PUT(HDRP(bp), PACK(size, 0));
  PUT(FTRP(bp), PACK(size, 0));
  PUT(FTRP(bp) + WSIZE, PACK(0, 1));
  return coalesce(bp);
}
int mm_init(void){
  for(int i = 0; i < NCLASS; i++){
    free_list[i] = NULL;
  }
  heap_listp = mem_sbrk(4 * WSIZE);//申请4字空间
  if(heap_listp == (void *)-1) return -1;
  PUT(heap_listp, 0);//开头4字节对齐，保证加入一个header后，数据内容是八字节对齐
  PUT(heap_listp + WSIZE, PACK(DSIZE, 1));//放入prologue header
  PUT(heap_listp + 2 * WSIZE, PACK(DSIZE, 1));//放入prologue footer
  PUT(heap_listp + 3 * WSIZE, PACK(0, 1));//放入epilogue header 防止越界
  heap_listp += DSIZE;//heap_listp后移
  if (extend_heap(CHUNKSIZE / WSIZE) == NULL) return -1;//开局扩容
  return 0;
}


static void *find_fit(size_t asize){
  int class_number = size_class(asize);//只找当前档和比自己大的档
  for( ; class_number < NCLASS; class_number++){
    for(void * bp = free_list[class_number]; bp != NULL; bp = NEXT_PTR(bp)){
      if(GET_SIZE(HDRP(bp)) >= asize){
        return bp;
      }
    }
  }
  return NULL;
}


static void place(void *bp, size_t asize){
  size_t old_size = GET_SIZE(HDRP(bp));//记录旧大小
  remove_free(bp, size_class(old_size));//摘掉一个节点，如果有剩余再插回去
  if(old_size - asize >= MINBLOCK){
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    void * free_start = NEXT_BLKP(bp);
    PUT(HDRP(free_start), PACK(old_size - asize, 0));
    PUT(FTRP(free_start), PACK(old_size - asize, 0));
    insert_free(free_start, size_class(old_size - asize));
  }
  else{
    PUT(HDRP(bp), PACK(old_size, 1));
    PUT(FTRP(bp), PACK(old_size, 1));
  }
}


static size_t adjust(size_t size){
  if(size <= DSIZE){
    return MINBLOCK;
  }
  return DSIZE * ((size + DSIZE + (DSIZE - 1)) / DSIZE);
}


void *mm_malloc (size_t size){
  if(size == 0) return NULL;
  size_t asize = adjust(size);
  char * bp = find_fit(asize);
  if(bp != NULL){
    place(bp, asize);
  }
  else{
    bp = extend_heap(MAX(asize, CHUNKSIZE) / WSIZE);
    if(bp == NULL) return NULL;
    place(bp, asize);
  }
  return bp;
}


void mm_free (void *ptr){
  if(ptr == NULL) return;
  size_t old_size = GET_SIZE(HDRP(ptr));
  PUT(HDRP(ptr), PACK(old_size, 0));
  PUT(FTRP(ptr), PACK(old_size, 0));
  coalesce(ptr);
}


void *mm_realloc(void *ptr, size_t size){
  if(ptr == NULL) return mm_malloc(size);
  if(size == 0){
    mm_free(ptr);
    return NULL;
  }
  size_t old_size = GET_SIZE(HDRP(ptr));
  size_t new_size = adjust(size);
  if(new_size <= old_size){
    if(old_size - new_size >= MINBLOCK){//能再切出一个块来
    PUT(HDRP(ptr), PACK(new_size, 1));
    PUT(FTRP(ptr), PACK(new_size, 1));
    PUT(HDRP(NEXT_BLKP(ptr)), PACK(old_size - new_size, 0));
    PUT(FTRP(NEXT_BLKP(ptr)), PACK(old_size - new_size, 0));
    coalesce(NEXT_BLKP(ptr));//合并检测
    return ptr;
    }
    else return ptr;//大小差不多
  }
  else{
    void * new_ptr = mm_malloc(size);
    if(new_ptr == NULL) return NULL;
    memcpy(new_ptr, ptr, old_size - DSIZE);
    mm_free(ptr);
    return new_ptr;
  }
}