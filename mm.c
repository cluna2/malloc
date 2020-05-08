#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "./memlib.h"
#include "./mm.h"
#include "./mminline.h"

// rounds up to the nearest multiple of WORD_SIZE
static inline size_t align(size_t size) {
    return (((size) + (WORD_SIZE - 1)) & ~(WORD_SIZE - 1));
}

static block_t *prolouge;
static block_t *epilouge;
int mm_check_heap(void);
int mm_check_free_list();
int mm_check_free_block_in_free_list(block_t *b_find);
block_t *mm_extend_heap(size_t size);
/*
 *                             _       _ _
 *     _ __ ___  _ __ ___     (_)_ __ (_) |_
 *    | '_ ` _ \| '_ ` _ \    | | '_ \| | __|
 *    | | | | | | | | | | |   | | | | | | |_
 *    |_| |_| |_|_| |_| |_|___|_|_| |_|_|\__|
 *                       |_____|
 *
 * initializes the dynamic storage allocator (allocate initial heap space)
 * arguments: none
 * returns: 0, if successful
 *         -1, if an error occurs
 */
int mm_init(void) {
    flist_first = NULL;
    if ((prolouge = (block_t *)mem_sbrk(TAGS_SIZE)) == (void *)-1) {
        fprintf(stderr, "Error: Prolouge allocation failed.");
        return -1;
    }
    if ((epilouge = (block_t *)mem_sbrk(TAGS_SIZE)) == (void *)-1) {
        fprintf(stderr, "Error: Epilouge allocation failed.");
        return -1;
    }
    block_set_size_and_allocated(prolouge, TAGS_SIZE, 1);
    block_set_size_and_allocated(epilouge, TAGS_SIZE, 1);
    return 0;
}

/*     _ __ ___  _ __ ___      _ __ ___   __ _| | | ___   ___
 *    | '_ ` _ \| '_ ` _ \    | '_ ` _ \ / _` | | |/ _ \ / __|
 *    | | | | | | | | | | |   | | | | | | (_| | | | (_) | (__
 *    |_| |_| |_|_| |_| |_|___|_| |_| |_|\__,_|_|_|\___/ \___|
 *                       |_____|
 *
 * allocates a block of memory and returns a pointer to that block's payload
 * arguments: size: the desired payload size for the block
 * returns: a pointer to the newly-allocated block's payload (whose size
 *          is a multiple of ALIGNMENT), or NULL if an error occurred
 */
void *mm_malloc(size_t size) {
    // return NULL if size is 0
    if (size == 0) {
        return NULL;
    }
    size = align(size);
    if (size + TAGS_SIZE < MINBLOCKSIZE) {
        size = MINBLOCKSIZE - TAGS_SIZE;
    }
    const size_t b_size = size + TAGS_SIZE;
    const size_t payload_size = size;
    // on first call, epilouge is right next to prolouge,
    // so  extend the heap
    if (epilouge == block_next(prolouge)) {
        block_t *new_block = mm_extend_heap(size);
        if (new_block == NULL) {
            return NULL;
        }
        pull_free_block(new_block);
        block_set_allocated(new_block, 1);
        return new_block->payload;
    } else {
        // check each free block for adequate size
        if (flist_first != NULL) {
            block_t *b = flist_first;
            do {
                if (block_size(b) >= b_size) {
                    pull_free_block(b);
                    block_set_allocated(b, 1);
                    // check if splitting is necessary
                    size_t diff = block_size(b) - b_size;
                    if (diff > MINBLOCKSIZE) {
                        block_set_size_and_allocated(b, b_size, 1);
                        block_t *new_fblock = block_next(b);
                        block_set_size_and_allocated(new_fblock, diff, 0);
                        insert_free_block(new_fblock);
                    }
                    // mm_check_heap();
                    return b->payload;
                }
                b = block_next_free(b);
            } while (b != flist_first);
            // no single free block is large enough, extend the heap
            block_t *new_block = mm_extend_heap(payload_size);
            if (new_block == NULL) {
                return NULL;
            }
            pull_free_block(new_block);
            block_set_allocated(new_block, 1);
            //mm_check_heap();
            return new_block->payload;
        } else {
            // if free list is empty, extend the heap
            block_t *new_block = mm_extend_heap(payload_size);
            if (new_block == NULL) {
                return NULL;
            }
            pull_free_block(new_block);
            block_set_allocated(new_block, 1);
            //mm_check_heap();
            return new_block->payload;
        }
    }
    return NULL;
}


/*                              __
 *     _ __ ___  _ __ ___      / _|_ __ ___  ___
 *    | '_ ` _ \| '_ ` _ \    | |_| '__/ _ \/ _ \
 *    | | | | | | | | | | |   |  _| | |  __/  __/
 *    |_| |_| |_|_| |_| |_|___|_| |_|  \___|\___|
 *                       |_____|
 *
 * frees a block of memory, enabling it to be reused later
 * arguments: ptr: pointer to the block's payload
 * returns: nothing
 */
void mm_free(void *ptr) {
    if (ptr == NULL) {
        return;
    }
    // get block from payload and contiguous blocks and sizes
    block_t *fblock = payload_to_block(ptr);
    size_t b_size = block_size(fblock);
    // printf("free ptr: %p\n", ptr);
    // printf("free size: %d\n", b_size);
    block_set_allocated(fblock, 0);
    block_t *b_prev = block_prev(fblock);
    block_t *b_next = block_next(fblock);
    size_t prev_size = block_size(b_prev);
    size_t next_size = block_size(b_next);
    // coalesce, checking if either contiguous block is free and 
    // combining if so
    if (!block_prev_allocated(fblock) && !block_next_allocated(fblock)) {
        // blocks to left and right free
        pull_free_block(b_prev);
        pull_free_block(b_next);
        block_set_size_and_allocated(
            b_prev, prev_size + b_size + next_size, 0);
        insert_free_block(b_prev);
    } else if (!block_prev_allocated(fblock) && block_next_allocated(fblock)) {
        // block to left free
        pull_free_block(b_prev);
        block_set_size_and_allocated(
            b_prev, prev_size + b_size, 0);
        insert_free_block(b_prev);
    } else if (block_prev_allocated(fblock) && !block_next_allocated(fblock)) {
        // block to right free
        pull_free_block(b_next);
        block_set_size_and_allocated(
            fblock, b_size + next_size, 0);
        insert_free_block(fblock);
    } else {
        // neither are free, just free fblock
        insert_free_block(fblock);
    }
    return;
}

/*
 *                                            _ _
 *     _ __ ___  _ __ ___      _ __ ___  __ _| | | ___   ___
 *    | '_ ` _ \| '_ ` _ \    | '__/ _ \/ _` | | |/ _ \ / __|
 *    | | | | | | | | | | |   | | |  __/ (_| | | | (_) | (__
 *    |_| |_| |_|_| |_| |_|___|_|  \___|\__,_|_|_|\___/ \___|
 *                       |_____|
 *
 * reallocates a memory block to update it with a new given size
 * arguments: ptr: a pointer to the memory block's payload
 *            size: the desired new payload size
 * returns: a pointer to the new memory block's payload
 */
void *mm_realloc(void *ptr, size_t size) {
    // TODO
    if (ptr == NULL) {
        block_t *to_return = mm_malloc(size);
        mm_check_heap();
        return to_return;
    }
    if (size == 0) {
        mm_free(ptr);
        mm_check_heap();
        return NULL;
    } 
    size = align(size);
    block_t *rblock = payload_to_block(ptr);
    size_t b_size = block_size(rblock);
    size_t requested_b_size = size + TAGS_SIZE;
    size_t current_payload_size = rblock->size;
    // if payload is small enough, ensure its block meets
    // minimum size
    if (size < MINBLOCKSIZE) {
        requested_b_size = MINBLOCKSIZE;
    }
    block_t *new_block;
    block_t *tmp_block;
    // rblock's size is large enough for the request
    if (b_size >= requested_b_size) {
        // diff of block sizes are large enough,
        // can shrink rblock to exact requested size
        if (b_size - requested_b_size > MINBLOCKSIZE) {
            block_set_size(rblock, requested_b_size);
            new_block = block_next(rblock);
            block_set_size_and_allocated(
                new_block, b_size - requested_b_size, 0);
            insert_free_block(new_block);
            mm_check_heap();
            return rblock->payload;
        } else {
            // diff of block sizes less than MINBLOCKSIZE
            // cannot shrink block to requested block size
            // and split
            mm_check_heap();
            return rblock->payload; 
        }
    // current block's size is insufficient
    // check neighbors for free status and if their 
    // additional size is enough for the request                
    } else if (requested_b_size > b_size) {
        block_t *b_next = block_next(rblock);
        block_t *b_prev = block_prev(rblock);
        size_t prev_size = block_size(b_prev);
        size_t next_size = block_size(b_next);
        size_t prev_and_rb_size = prev_size + b_size;
        size_t next_and_rb_size = next_size + b_size;
        size_t all_three_size = prev_size + b_size + next_size;

        // if next block is free and sum of sizes of rblock
        // and its next block are large enough, combine them
        if (block_prev_allocated(rblock) && !block_next_allocated(rblock)
            && next_and_rb_size > requested_b_size) {
            pull_free_block(b_next);
            // if sum of sizes > MINBLOCKSIZE, splitting is possible
            if (next_and_rb_size - requested_b_size > MINBLOCKSIZE) {
                block_set_size_and_allocated(
                    rblock, requested_b_size, 1);
                new_block = block_next(rblock);
                block_set_size_and_allocated(
                    new_block, next_and_rb_size - requested_b_size, 0);
                insert_free_block(new_block);
                mm_check_heap();
                return rblock->payload;
            } else {
            // otherwise dont split, just set size as their sum
                block_set_size_and_allocated(
                    rblock, next_and_rb_size, 1);
                mm_check_heap();
                return rblock->payload;
            }
        // if prev block is free and sum of sizes of rblock
        // and its prev block are large enough, combine them        
        } else if (!block_prev_allocated(rblock) && block_allocated(rblock)
            && prev_and_rb_size > requested_b_size) {
            // move the payload from ptr over to start of payload
            // of previous block and free rblock
            mm_check_heap();
            pull_free_block(b_prev);
            block_set_allocated(rblock, 0);
            memmove(b_prev->payload, ptr, current_payload_size);
            block_set_allocated(rblock, 1);
            mm_free(ptr);
            // printf("%p\n",ptr);
            // printf("%p\n", rblock);
            // printf("Block size after memmove: %d\n", (int) b_size);
            // if sum of sizes > MINBLOCKSIZE, splitting is possible
            if (prev_and_rb_size - requested_b_size > MINBLOCKSIZE) {
                block_set_size_and_allocated(
                    b_prev, requested_b_size, 1);
                new_block = block_next(b_prev);
                block_set_size_and_allocated(
                    new_block, prev_and_rb_size - requested_b_size, 0);
                insert_free_block(new_block);
                mm_check_heap();
                return b_prev->payload;
            } else {
            // not able to split, set size to sum of prev and rblock's sizes
                block_set_size_and_allocated(
                    b_prev, prev_and_rb_size, 1);
                mm_check_heap();
                return b_prev->payload;
            }
        // both blocks on either end are free and their combined size
        // is large enough for the request
        } else if (!block_prev_allocated(rblock) && !block_allocated(rblock)
            && all_three_size > requested_b_size) {
            // pull blocks, move payload, free rblock
            mm_check_heap();
            pull_free_block(b_prev);
            pull_free_block(b_next);
            block_set_allocated(rblock, 0);
            memmove(b_prev->payload, ptr, current_payload_size);
            block_set_allocated(rblock, 1);
            mm_free(ptr);
            // printf("%p\n",ptr);
            // printf("%p\n", rblock);
            // printf("Block size after memmove: %d\n" , (int) b_size);
            mm_free(rblock->payload);
            // check if splitting is possible
            if (all_three_size - requested_b_size > MINBLOCKSIZE) {
                block_set_size_and_allocated(
                    b_prev, requested_b_size, 1);
                new_block = block_next(b_prev);
                block_set_size_and_allocated(
                    new_block, all_three_size - requested_b_size, 0);
                insert_free_block(new_block);
                mm_check_heap();
                return b_prev->payload;
            } else {
                // not able to split, set size to sum of all three
                block_set_size_and_allocated(
                    b_prev, prev_and_rb_size, 1);
                mm_check_heap();
                return b_prev->payload;
            }
        }

        // otherwise, need to allocate more memory 
        new_block = mm_malloc(size);
        if (new_block == NULL) {
            // cannot allocate memory
            mm_check_heap();
            return NULL;
        }
        block_set_allocated(rblock, 0);
        memmove(new_block, ptr, current_payload_size);
        block_set_allocated(rblock, 1);
        mm_free(ptr);
        // printf("%p\n",ptr);
        // printf("%p\n", rblock);
        // printf("Block size after memmove: %d\n", (int) b_size);
        // mm_free(rblock->payload);
        mm_check_heap();
        return new_block;
    }
    mm_check_heap();
    return NULL;
}

/*
 * checks the state of the heap for internal consistency and prints informative
 * error messages
 * arguments: none
 * returns: 0, if successful
 *          nonzero, if the heap is not consistent
 */
int mm_check_heap(void) {
    // printf("\n\nChecking Heap\n\n");
    // check if prolouge and epilouge are at the boundaries of the heap
    assert(mem_heap_lo() == prolouge);
    assert(((char *)mem_heap_hi() + 1)
         == ((char *)epilouge + TAGS_SIZE));
    // printf("Heap size: %d\n",
    //     (int)((char *)mem_heap_hi() - (char *)mem_heap_lo() + 1));
    block_t *b = prolouge;
    block_t *b_prev = NULL;
    block_t *b_next = block_next(b);
    int size = (int) block_size(b);
    printf("\nProlouge at  \t (%p, %p) \
        with size %d\n", (void *)b, (void*)((char *)b + size), size);
    printf("Epilouge at \t (%p, %p) \
        with size %d\n",
         (void *)epilouge, (void *)((char*)mem_heap_hi()+1), (int)TAGS_SIZE);
    char msg[1024];
    b = b_next;
    if (b_next == epilouge) {
        return 0;
    }
    // iterate through each block in the heap and perform various checks
    while (b_next != epilouge) {
        b = b_next;
        b_prev = block_prev(b);
        b_next = block_next(b_next);
        size = (int) block_size(b);
        char *lo = (char *)b;
        char *hi = (char *)b + size;
        // check if block is in the heap
        if ((lo < (char *)mem_heap_lo()) || (lo > (char *)mem_heap_hi()) ||
            (hi < (char *)mem_heap_lo()) || (hi >= (char *)mem_heap_hi())) {
            sprintf(msg, "Block (%p:%p) lies outside heap (%p:%p)", lo, hi,
                mem_heap_lo(), mem_heap_hi());
            exit(1);
        }
        // check that a block's size is above the minimum size
        if (size < (int)MINBLOCKSIZE) {
            fprintf(stderr, "Block (%p, %p) has size %d \
                smaller than the minimum size %d\n", lo, hi, size,
                (int)MINBLOCKSIZE);
            exit(1);
        }


        // check that the tags on both ends match
        if (size != (int) block_end_size(b)) {
            fprintf(stderr, "Beginning and end sizes don't match");
            exit(1);
        }

        // check that blocks are properly aligned
        char *prev_high = (char *)b_prev + (int)block_prev_size(b);
        char *next_lo = (char *)b_next;
        if ((prev_high != lo) || (next_lo != hi)) {
            fprintf(stderr,
                "Error: Block (%p, %p) is not aligned with previous block's \n\
                end (%p) or with next block's start (%p)",
                lo, hi, prev_high, next_lo);
            exit(1);
        }


        //check to see if blocks are contiguous
        if (!(block_next(block_prev(b)) == b)) {
            fprintf(stderr, "The block at (%p, %p) \
                is not contiguous with the previous \
                block at (%p, %p)", lo, hi, 
                (void *)b_prev,
                (void *)((char *)b_prev + (int)block_prev_size(b)));
            exit(1);
                  
        } else if (!(block_prev(block_next(b)) == b)) {
            fprintf(stderr, "The block at (%p, %p) \
                is not contiguous with the next \
                block at (%p, %p)", lo, hi, 
                (void *)b_next,
                (void *)((char *)b_next + (int)block_next_size(b)));
            exit(1);
        }
        // check if block is alloacated
        if (!block_allocated(b)) {
            printf("Free block at \t\t (%p, %p) with size %d\n",
                lo, hi, size);

            
            // check if prev or next block is also free
            // if so, then there are contiguous free blocks
            // that aren't joined
            if (!block_prev_allocated(b)) {
                fprintf(stderr,
                    "Free previous contiguous block \n\
                    at (%p, %p) with size %d next to current block\n", 
                    (void *)b_prev,
                    (void *)((char *)b_prev + (int)block_prev_size(b)),
                    (int)block_prev_size(b));
                exit(1);
            } else if (!block_next_allocated(b)) {
                fprintf(stderr,
                    "Free next contiguous block \n\
                    at (%p, %p) with size %d next to current block\n", 
                    (void *)b_next,
                    (void *)((char *)b_next + (int)block_next_size(b)),
                    (int)block_next_size(b));
                exit(1);
            } 
            //check if each free block is in the free list
            if (flist_first != NULL) {
                assert(mm_check_free_block_in_free_list(b) == 1);
            }

            // check if the payload size is large enough for prev and next pointers
            if (b->size < TAGS_SIZE) {
                fprintf(stderr, "Free Block at (%p, %p) \
                    of size %d has payload size %d which is smaller \
                    than needed for its pointers %d\n", 
                    lo, hi, size, (int)b->size, (int)TAGS_SIZE);
                exit(1);
            }
        } else {
            printf("Allocated block at \t (%p, %p) with size %d\n",
                lo, hi, size);
        }
        // printf("b_next == epilouge: %d\n", (int)(b_next == epilouge));
    }
    assert(mm_check_free_list() == 1);

    // printf("\n\nFinished Checking Heap\n\n");
    return 0;
}


/*
 * Check if each block in the free list is marked as free
 * Return 1 if all blocks in free list are marked as free or
 * if the list is empty and 0 otherwise
 */
int mm_check_free_list() {
    // iterate through free list and check each block is marked as free
    if (flist_first != NULL) {
        block_t *b = flist_first;
        while(block_next_free(b) != flist_first) {
            // printf("Checking free list\n");
            if (block_allocated(b)) {
                fprintf(stderr,
                    "Block in free list at (%p, %p) \
                    of size %d is not marked as free\n", (void *)b,
                    (void *)((char *)b+block_size(b)), 
                    (int) block_size(b));
                return 0;
            }
            b = block_next_free(b);
        }
    }
    return 1;
}

/*
 * Check if a block marked as free is in the free list
 * Returns 1 if true and 0 otherwise.
 */
int mm_check_free_block_in_free_list(block_t *b_find) {
    assert(!block_allocated(b_find));
    block_t *b = flist_first;
    // if head is free, return immedidately
    if (b_find == b) {
        return 1;
    }
    // check if we reached start/end of circle
    while (block_next_free(b) != flist_first) {
        if (b_find == b) {
            return 1;
        }
        b = block_next_free(b);
    }
    fprintf(stderr, "Free block (%p, %p) of size \
        %d is not in the free list\n", (void *)b_find,
        (void *)((char *)b_find+block_size(b_find)),
        (int)block_size(b_find));
    return 0;
}


/*
 *  Extends the heap.
 *  Switches the epilouge back to the end of the heap.
 *  Returns the penultimate block (block next to the epilouge).
 */
block_t *mm_extend_heap(size_t size) {
    size_t new_size = size + 2*TAGS_SIZE;
    if (mem_sbrk(new_size) == (void *)-1) {
        fprintf(stderr, "Error: Heap extension failed.");
        //mm_check_heap();
        return NULL;
    }
    // epilouge is now freed, check if block preceeding epilouge is free
    // if so, coalesce with both epilouge and that free block
    // otherwise, coalesce with just epilouge
    block_t *prev = block_prev(epilouge);
    block_t *return_b;
    if (!block_allocated(prev)) {
        pull_free_block(prev);
        block_set_size_and_allocated(
            prev, block_size(prev) + new_size, 0);
        insert_free_block(prev);
        return_b = prev;
    } else {
        block_set_size_and_allocated(epilouge, new_size, 0);
        insert_free_block(epilouge);
        return_b = epilouge;
    }
    // move epilouge to the end and reallocate it
    epilouge = block_next(return_b);
    block_set_size_and_allocated(epilouge, TAGS_SIZE, 1);
    //mm_check_heap();
    return return_b;
}