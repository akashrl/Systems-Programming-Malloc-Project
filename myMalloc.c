#include <errno.h>
#include <pthread.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "myMalloc.h"
#include "printing.h"

/* Due to the way assert() prints error messges we use out own assert function
 * for deteminism when testing assertions
 */
#ifdef TEST_ASSERT
  inline static void assert(int e) {
    if (!e) {
      const char * msg = "Assertion Failed!\n";
      write(2, msg, strlen(msg));
      exit(1);
    }
  }
#else
  #include <assert.h>
#endif

const size_t longSize = sizeof(size_t);

/*
 * Mutex to ensure thread safety for the freelist
 */
static pthread_mutex_t mutex;

/*
 * Array of sentinel nodes for the freelists
 */
header freelistSentinels[N_LISTS];

/*
 * Pointer to the second fencepost in the most recently allocated chunk from
 * the OS. Used for coalescing chunks
 */
header * lastFencePost;

/*
 * Pointer to maintian the base of the heap to allow printing based on the
 * distance from the base of the heap
 */ 
void * base;

/*
 * List of chunks allocated by  the OS for printing boundary tags
 */
header * osChunkList [MAX_OS_CHUNKS];
size_t numOsChunks = 0;

/*
 * direct the compiler to run the init function before running main
 * this allows initialization of required globals
 */
static void init (void) __attribute__ ((constructor));

// Helper functions for manipulating pointers to headers
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off);
static inline header * get_left_header(header * h);
static inline header * ptr_to_header(void * p);

// Helper functions for allocating more memory from the OS
static inline void initialize_fencepost(header * fp, size_t left_size);
static inline void insert_os_chunk(header * hdr);
static inline void insert_fenceposts(void * raw_mem, size_t size);
static header * allocate_chunk(size_t size);
static inline header * expand_heap_size(size_t size);

// Helper functions for freeing a block
static inline void deallocate_object(void * p);
static inline void update_freelist(header * current, size_t size, int flag, header * old);

// Helper functions for allocating a block
static inline header * allocate_object(size_t raw_size);
static inline header * split_block(header *block, size_t block_size);

// Helper functions for verifying that the data structures are structurally 
static inline header * detect_cycles();
static inline header * verify_pointers();
static inline bool verify_freelist();
static inline header * verify_chunk(header * chunk);
static inline bool verify_tags();

static inline void remove_from_freelist(header *hdr);
static inline void insert_into_freelist(header *freelist, header *hdr);

static void init();

/**
 * @brief Helper function to retrieve a header pointer from a pointer and an 
 *        offset
 *
 * @param ptr base pointer
 * @param off number of bytes from base pointer where header is located
 *
 * @return a pointer to a header offset bytes from pointer
 */
static inline header * get_header_from_offset(void * ptr, ptrdiff_t off) {
	return (header *)((char *) ptr + off);
}

/**
 * @brief Helper function to get the header to the right of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
header * get_right_header(header * h) {
	return get_header_from_offset(h, get_size(h));
}

/**
 * @brief Helper function to get the header to the left of a given header
 *
 * @param h original header
 *
 * @return header to the right of h
 */
inline static header * get_left_header(header * h) {
  return get_header_from_offset(h, -h->left_size);
}

/**
 * @brief Fenceposts are marked as always allocated and may need to have
 * a left object size to ensure coalescing happens properly
 *
 * @param fp a pointer to the header being used as a fencepost
 * @param left_size the size of the object to the left of the fencepost
 */
inline static void initialize_fencepost(header * fp, size_t left_size) {
	set_state(fp,FENCEPOST);
	set_size(fp, ALLOC_HEADER_SIZE);
	fp->left_size = left_size;
}

/**
 * @brief Helper function to maintain list of chunks from the OS for debugging
 *
 * @param hdr the first fencepost in the chunk allocated by the OS
 */
inline static void insert_os_chunk(header * hdr) {
  if (numOsChunks < MAX_OS_CHUNKS) {
    osChunkList[numOsChunks++] = hdr;
  }
}

/**
 * @brief given a chunk of memory insert fenceposts at the left and 
 * right boundaries of the block to prevent coalescing outside of the
 * block
 *
 * @param raw_mem a void pointer to the memory chunk to initialize
 * @param size the size of the allocated chunk
 */
inline static void insert_fenceposts(void * raw_mem, size_t size) {
  // Convert to char * before performing operations
  char * mem = (char *) raw_mem;

  // Insert a fencepost at the left edge of the block
  header * leftFencePost = (header *) mem;
  initialize_fencepost(leftFencePost, ALLOC_HEADER_SIZE);

  // Insert a fencepost at the right edge of the block
  header * rightFencePost = get_header_from_offset(mem, size - ALLOC_HEADER_SIZE);
  initialize_fencepost(rightFencePost, size - 2 * ALLOC_HEADER_SIZE);
}

/**
 * @brief Allocate another chunk from the OS and prepare to insert it
 * into the free list
 *
 * @param size The size to allocate from the OS
 *
 * @return A pointer to the allocable block in the chunk (just after the 
 * first fencpost)
 */
static header * allocate_chunk(size_t size) {
  void * mem = sbrk(size);

  insert_fenceposts(mem, size);

  header * hdr = (header *) ((char *)mem + ALLOC_HEADER_SIZE);
  set_state(hdr, UNALLOCATED);
  set_size(hdr, size - 2 * ALLOC_HEADER_SIZE);
  hdr->left_size = ALLOC_HEADER_SIZE;
  return hdr;
}

/**
 * remove hdr from its current list
 */
static inline void remove_from_freelist(header *hdr) {
    hdr->next->prev = hdr->prev;
    hdr->prev->next = hdr->next;
}

/**
 * Insert hdr to the head of freelist
 */
static inline void insert_into_freelist(header *freelist, header *hdr) {
	freelist->next->prev = hdr;
	hdr->next = freelist->next;
	freelist->next = hdr;
	hdr->prev = freelist;
}

/**
 * split block
 */
static inline header * split_block(header *block, size_t block_size)
{
	set_size(block, get_size(block) - block_size);

	header * newHeader = get_right_header(block);

	set_size(newHeader, block_size);
	newHeader->left_size = get_size(block);
	set_state(newHeader, ALLOCATED);

	header *rightHeader = get_right_header(newHeader);
	rightHeader->left_size = get_size(newHeader);

	int i = (get_size(block) -ALLOC_HEADER_SIZE)/longSize - 1;

	if(i<N_LISTS-1)
	{
		remove_from_freelist(block);

		header * freelist = &freelistSentinels[i];

		insert_into_freelist(freelist, block);
	}

	return newHeader;
}

/**
 * expand the heap size
 */
static inline header * expand_heap_size(size_t size)
{

	header * new_chunk = allocate_chunk(ARENA_SIZE);

	header * lastheader = get_header_from_offset(new_chunk, -2*ALLOC_HEADER_SIZE);
	header * rightblock;

	if (get_state(lastheader) != FENCEPOST) // if not connected with the previous chunk
	{
		header *prevFencePost = get_header_from_offset(new_chunk, -ALLOC_HEADER_SIZE);
		insert_os_chunk(prevFencePost);

		header *freelist = &freelistSentinels[N_LISTS-1];

		insert_into_freelist(freelist, new_chunk);
	}
	else // if connected with previous chunk
	{
		// need to merge two chunks
		header * lastblock = get_left_header(lastheader);

		if (get_state(lastblock) == UNALLOCATED)
		{
			set_size(lastblock, get_size(lastblock) + get_size(new_chunk) + 2*ALLOC_HEADER_SIZE);

			remove_from_freelist(lastblock);

			header *freelist = &freelistSentinels[N_LISTS-1];
			insert_into_freelist(freelist, lastblock);

			rightblock = get_right_header(lastblock);
			rightblock->left_size = get_size(lastblock);
		}
		else
		{
			set_state(lastheader, UNALLOCATED);
			set_size(lastheader, get_size(lastheader) + get_size(new_chunk) + ALLOC_HEADER_SIZE);

	                header *freelist = &freelistSentinels[N_LISTS-1];
			insert_into_freelist(freelist, lastheader);

			rightblock = get_right_header(lastheader);
                        rightblock->left_size = get_size(lastheader);
		}
	}

	return allocate_object(size);
}

/**
 * @brief Helper allocate an object given a raw request size from the user
 *
 * @param raw_size number of bytes the user needs
 *
 * @return A block satisfying the user's request
 */
static inline header * allocate_object(size_t raw_size) {
	size_t c;
	
	if (raw_size == 0) return NULL;

	if((c = (raw_size % longSize)) != 0) // if not an 8-byte modulo
		raw_size += longSize-c; // calculate block size rounding up to next 8-byte modulo

	size_t block_size = ALLOC_HEADER_SIZE + raw_size;

	if (block_size< sizeof(header)) block_size = sizeof(header); // at least new block_size >= sizeof(header)

	if (block_size <= (N_LISTS-1)*longSize + ALLOC_HEADER_SIZE) // if new block is fit to small freelists
	{
		int i, idx = (block_size-ALLOC_HEADER_SIZE)/longSize - 1; // freelists index
		for(i = idx;i < N_LISTS-1; i++) {
			header * freelist = &freelistSentinels[i];
			if(freelist->next != freelist) // if not empty
			{
				header * newblock = freelist->next;
				if (get_size(newblock) < block_size + sizeof(header)) // if no need to split
				{
					set_state(newblock, ALLOCATED);
					newblock->prev->next = newblock->next;
					newblock->next->prev = freelist;
					return (header *)((char *)newblock+ALLOC_HEADER_SIZE);
				}
				else //should split
				{
					header *smallblock = split_block(newblock,block_size);
					return (header *)((char *)smallblock + ALLOC_HEADER_SIZE);
				}
			}
		}
	}

	// need to insert in the last list
	header *freelist = &freelistSentinels[N_LISTS-1];

	header *newblock = freelist->next;

	while(newblock != freelist) //check each block
	{
		if (get_size(newblock) >= block_size && get_size(newblock) < block_size+sizeof(header)) // no need to split
		{
			set_state(newblock, ALLOCATED);
			remove_from_freelist(newblock);
			return (header *)((char *)newblock+ALLOC_HEADER_SIZE);
		}
		else if (get_size(newblock) >= block_size+sizeof(header)) //need to split
		{
			header *smallblock = split_block(newblock,block_size);
			return (header *)((char *)smallblock+ALLOC_HEADER_SIZE);
		}
		newblock = newblock->next;
	}

	//need to expand size
	return expand_heap_size(raw_size);
}



/**
 * @brief Helper to get the header from a pointer allocated with malloc
 *
 * @param p pointer to the data region of the block
 *
 * @return A pointer to the header of the block
 */
static inline header * ptr_to_header(void * p) {
  return (header *)((char *) p - ALLOC_HEADER_SIZE);
  
}

/**
 * @brief Helper to manage deallocation of a pointer returned by the user
 *
 * @param p The pointer returned to the user by a call to malloc
 */
static inline void deallocate_object(void * p) {
	if(p == NULL)
		return;

	header * centralHeader = get_header_from_offset(p,-ALLOC_HEADER_SIZE);

	header * rightHeader = get_right_header(centralHeader);
	header * leftHeader = get_left_header(centralHeader);

	int size,flag = 0;

	if (get_state(centralHeader) == UNALLOCATED)
	{
		fprintf(stderr, "Double Free Detected\n");
		assert(0);
	}
	else if (get_state(rightHeader) == UNALLOCATED && get_state(leftHeader) == UNALLOCATED)
	{
		//left and right blocks are both unallocated
		set_state(centralHeader, UNALLOCATED);

		if (get_size(leftHeader) > (N_LISTS-1)*longSize + ALLOC_HEADER_SIZE)
			flag = 1;

		set_size(leftHeader, get_size(leftHeader) + get_size(centralHeader) + get_size(rightHeader));
		size = get_size(leftHeader);

		remove_from_freelist(rightHeader);
		remove_from_freelist(leftHeader);

		update_freelist(leftHeader,size,flag,leftHeader);

		header *right = get_right_header(leftHeader);
		right->left_size = size;
	}
	else if (get_state(leftHeader) == UNALLOCATED)
	{
		//left block is unallocated
		set_state(centralHeader, UNALLOCATED);

		if (get_size(leftHeader) > ALLOC_HEADER_SIZE+ (N_LISTS-1)*longSize)
                        flag = 1;

		set_size(leftHeader, get_size(leftHeader) + get_size(centralHeader));
		size = get_size(leftHeader);

		remove_from_freelist(leftHeader);

		update_freelist(leftHeader,size,flag,leftHeader);

                header *right = get_right_header(leftHeader);
                right->left_size = size;
	}
	else if (get_state(rightHeader) == UNALLOCATED)
	{
		//right block is unallocated
		set_state(centralHeader, UNALLOCATED);

		if (get_size(rightHeader) > ALLOC_HEADER_SIZE + (N_LISTS-1)*longSize)
                        flag = 1;

		set_size(centralHeader, get_size(centralHeader) + get_size(rightHeader));
		size = get_size(centralHeader);

		remove_from_freelist(rightHeader);

		update_freelist(centralHeader,size,flag,rightHeader);

                header *right = get_right_header(centralHeader);
                right->left_size = size;
	}
	else
	{
		set_state(centralHeader, UNALLOCATED);
		size = get_size(centralHeader);
                update_freelist(centralHeader,size,flag,rightHeader);
	}
}

static inline void update_freelist(header * current, size_t size, int flag, header * old)
{
	if(flag == 0)
	{
		int i;
		header *freelist = NULL;
		if(size<=ALLOC_HEADER_SIZE + (N_LISTS-1)*longSize) {
			i = (size - ALLOC_HEADER_SIZE)/longSize-1;
			freelist = &freelistSentinels[i];
		}
		else
			freelist = &freelistSentinels[N_LISTS-1];
	
		insert_into_freelist(freelist, current);
	}
	else
	{
		old->next->prev = current;
		current->next = old->next;
		old->prev->next = current;
		current->prev = old->prev;
	}
}

/**
 * @brief Helper to detect cycles in the free list
 * https://en.wikipedia.org/wiki/Cycle_detection#Floyd's_Tortoise_and_Hare
 *
 * @return One of the nodes in the cycle or NULL if no cycle is present
 */
static inline header * detect_cycles() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * slow = freelist->next, * fast = freelist->next->next; 
         fast != freelist; 
         slow = slow->next, fast = fast->next->next) {
      if (slow == fast) {
        return slow;
      }
    }
  }
  return NULL;
}

/**
 * @brief Helper to verify that there are no unlinked previous or next pointers
 *        in the free list
 *
 * @return A node whose previous and next pointers are incorrect or NULL if no
 *         such node exists
 */
static inline header * verify_pointers() {
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    for (header * cur = freelist->next; cur != freelist; cur = cur->next) {
      if (cur->next->prev != cur || cur->prev->next != cur) {
        return cur;
      }
    }
  }
  return NULL;
}

/**
 * @brief Verify the structure of the free list is correct by checkin for 
 *        cycles and misdirected pointers
 *
 * @return true if the list is valid
 */
static inline bool verify_freelist() {
  header * cycle = detect_cycles();
  if (cycle != NULL) {
    fprintf(stderr, "Cycle Detected\n");
    print_sublist(print_object, cycle->next, cycle);
    return false;
  }

  header * invalid = verify_pointers();
  if (invalid != NULL) {
    fprintf(stderr, "Invalid pointers\n");
    print_object(invalid);
    return false;
  }

  return true;
}

/**
 * @brief Helper to verify that the sizes in a chunk from the OS are correct
 *        and that allocated node's canary values are correct
 *
 * @param chunk AREA_SIZE chunk allocated from the OS
 *
 * @return a pointer to an invalid header or NULL if all header's are valid
 */
static inline header * verify_chunk(header * chunk) {
	if (get_state(chunk) != FENCEPOST) {
		fprintf(stderr, "Invalid fencepost\n");
		print_object(chunk);
		return chunk;
	}
	
	for (; get_state(chunk) != FENCEPOST; chunk = get_right_header(chunk)) {
		if (get_size(chunk)  != get_right_header(chunk)->left_size) {
			fprintf(stderr, "Invalid sizes\n");
			print_object(chunk);
			return chunk;
		}
	}
	
	return NULL;
}

/**
 * @brief For each chunk allocated by the OS verify that the boundary tags
 *        are consistent
 *
 * @return true if the boundary tags are valid
 */
static inline bool verify_tags() {
  for (size_t i = 0; i < numOsChunks; i++) {
    header * invalid = verify_chunk(osChunkList[i]);
    if (invalid != NULL) {
      return invalid;
    }
  }

  return NULL;
}

/**
 * @brief Initialize mutex lock and prepare an initial chunk of memory for allocation
 */
static void init() {
  // Initialize mutex for thread safety
  pthread_mutex_init(&mutex, NULL);

#ifdef DEBUG
  // Manually set printf buffer so it won't call malloc when debugging the allocator
  setvbuf(stdout, NULL, _IONBF, 0);
#endif // DEBUG

  // Allocate the first chunk from the OS
  header * block = allocate_chunk(ARENA_SIZE);

  header * prevFencePost = get_header_from_offset(block, -ALLOC_HEADER_SIZE);
  insert_os_chunk(prevFencePost);

  lastFencePost = get_right_header(block);

  // Set the base pointer to the beginning of the first fencepost in the first
  // chunk from the OS
  base = ((char *) block) - ALLOC_HEADER_SIZE; //sizeof(header);

  // Initialize freelist sentinels
  for (int i = 0; i < N_LISTS; i++) {
    header * freelist = &freelistSentinels[i];
    freelist->next = freelist;
    freelist->prev = freelist;
  }

  // Insert first chunk into the free list
  header * freelist = &freelistSentinels[N_LISTS - 1];
  freelist->next = block;
  freelist->prev = block;
  block->next = freelist;
  block->prev = freelist;
}

/* 
 * External interface
 */
void * my_malloc(size_t size) {
  pthread_mutex_lock(&mutex);
  header * hdr = allocate_object(size); 
  pthread_mutex_unlock(&mutex);
  return hdr;
}

void * my_calloc(size_t nmemb, size_t size) {
  return memset(my_malloc(size * nmemb), 0, size * nmemb);
}

void * my_realloc(void * ptr, size_t size) {
  void * mem = my_malloc(size);
  memcpy(mem, ptr, size);
  my_free(ptr);
  return mem; 
}

void my_free(void * p) {
  pthread_mutex_lock(&mutex);
  deallocate_object(p);
  pthread_mutex_unlock(&mutex);
}

bool verify() {
  return verify_freelist() && verify_tags();
}
