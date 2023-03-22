#include "cachelab.h"
#include <assert.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

const int LINELEN = 21;
const long MAX_SIZE = 16;

typedef struct line {
    int valid;
    long tag;
    int dirty;
    int timeStamp;
} Line;

Line **cache = NULL;
int hit = 0, miss = 0, eviction = 0, dirtyInCache = 0, dirtyEvicted = 0,
    time = 0, S, B, E;

static void print_help() {
    printf("-h,  show this help message and exit\n");
    printf("-v,  Verbose mode: report effects of each memory operation\n");
    printf("-s <s>,  Number of set index bits (there are 2**s sets)\n");
    printf("-b <b>,  Number of block  bits (there are 2**b blocks)\n");
    printf("-E <E>,  Number of lines per set (associativity)\n");
    printf("-t <trace>,  File name of the memory trace to process\n");
    printf("\n");
    printf("The -s, -b, -E and -t options must be supplied for all "
           "simulations.\n");
}

/** Check if the command line input is valid.
 *
 * @param set bits, block offset bits, number of lines per set, file name.
 * @return None.
 */
static void checkValidInput(int s, int b, int E, char *t) {
    // wrong/missing inputs
    if (s < 0 || b < 0 || E <= 0 || !t) {
        printf("Incorrect Invocations.\n");
        exit(1);
    }

    // number of bits exceeds the address space
    if (s + b > 64) {
        printf("Failed to allocate memory.\n");
        exit(1);
    }
}

/** Initialize the params of the cache.
 *
 * @param set bits, block offset bits, number of lines per set.
 * @return None.
 */
void init_cache(int s, int b, int E) {
    S = 1 << s;
    B = 1 << b;
    cache = (Line **)malloc(sizeof(Line *) * (unsigned long)S);

    // initializa every line
    for (int i = 0; i < S; i++) {
        cache[i] = (Line *)malloc(sizeof(Line) * (unsigned long)E);
        for (int j = 0; j < E; j++) {
            cache[i][j].valid = 0;
            cache[i][j].tag = 0;
            cache[i][j].dirty = 0;
            cache[i][j].timeStamp = 0;
        }
    }
}

/** find the line matches with the address.
 *
 * @param tag bits, set index.
 * @return the line index of the matched line in the set, or -1 if no matched
 * line.
 */
int find_matched_line(long tag, int setIndex) {
    for (int i = 0; i < E; i++) {
        if (cache[setIndex][i].valid == 1 && cache[setIndex][i].tag == tag) {
            return i;
        }
    }
    return -1;
}

/** find the first empty line in the set.
 *
 * @param set index.
 * @return the line index of the first empty line in the set, or -1 if the set
 * is full.
 */
int find_empty_line(int setIndex) {
    for (int i = 0; i < E; i++) {
        if (cache[setIndex][i].valid == 0) {
            return i;
        }
    }
    return -1;
}

/** find the least recently used line in the set.
 *
 * @param set index.
 * @return the line index of LRU line.
 */
int find_LRU(int setIndex) {
    int minTime = 9999999, minIndex = -1;
    for (int i = 0; i < E; i++) {
        int time = cache[setIndex][i].timeStamp;
        if (time < minTime) {
            minTime = time;
            minIndex = i;
        }
    }
    return minIndex;
}

/** Set the line according to the address.
 *
 * @param tag bits, set index of the address, line index of the address.
 * @return None.
 */
void set_cache(long tag, int setIndex, int lineIndex) {
    cache[setIndex][lineIndex].valid = 1;
    cache[setIndex][lineIndex].tag = tag;
    cache[setIndex][lineIndex].dirty = 0;
    cache[setIndex][lineIndex].timeStamp = time;
}

/** Load the address into cache.
 *
 * @param tag bits and set index of the address.
 * @return None.
 */
void load_cache(long tag, int setIndex) {
    time++;
    int lineIndex = find_matched_line(tag, setIndex);

    // address results in a hit; update timestamp
    if (lineIndex != -1) {
        hit++;
        cache[setIndex][lineIndex].timeStamp = time;
    }
    // address results in a miss; update line and timestamp
    else {
        miss++;
        int newLineIndex = find_empty_line(setIndex);

        // no empty lines; evict a line by LRU
        if (newLineIndex == -1) {
            newLineIndex = find_LRU(setIndex);
            if (cache[setIndex][newLineIndex].dirty == 1) {
                dirtyEvicted++;
                dirtyInCache--;
            }
            eviction++;
        }
        set_cache(tag, setIndex, newLineIndex);
    }
}

/** Store the address into cache.
 *
 * @param tag bits and set index of the address.
 * @return None.
 */
void store_cache(long tag, int setIndex) {
    time++;
    int lineIndex = find_matched_line(tag, setIndex);

    // address results in a hit; update timestamp
    if (lineIndex != -1) {
        hit++;
        cache[setIndex][lineIndex].timeStamp = time;

        // update the dirty bit
        if (cache[setIndex][lineIndex].dirty == 0) {
            dirtyInCache++;
            cache[setIndex][lineIndex].dirty = 1;
        }
    }
    // address results in a miss; update line and timestamp
    else {
        miss++;
        int newLineIndex = find_empty_line(setIndex);
        // no empty lines; evict a line by LRU
        if (newLineIndex == -1) {
            newLineIndex = find_LRU(setIndex);
            if (cache[setIndex][newLineIndex].dirty == 1) {
                dirtyEvicted++;
            }
            eviction++;
        }

        if (cache[setIndex][newLineIndex].dirty == 0) {
            dirtyInCache++;
        }
        set_cache(tag, setIndex, newLineIndex);
        cache[setIndex][newLineIndex].dirty = 1;
    }
}

/** Process a memory -access trace file.
 *
 * @param trace Name of the trace file to process.
 * @return 0 if successful , 1 if there were errors.
 */
int process_trace_file(const char *trace, int s, int E, int b) {
    FILE *tfp = fopen(trace, "rt");
    if (!tfp) {
        fprintf(stderr, "Error opening'%s'\n", trace);
        exit(1);
    }
    int size, parse_error = 0;
    unsigned long addr;
    char action;

    // scan each line in the trace, and act accordingly
    while (fscanf(tfp, " %c %lx,%d", &action, &addr, &size) > 0) {
        if (addr < 0) {
            printf("Address %lu is out of range\n", addr);
            exit(1);
        }
        if (size < 0 || size >= MAX_SIZE) {
            printf("Size is out of range\n");
            exit(1);
        }

        long tag = (long)(addr >> (unsigned int)(s + b));
        int setIndex = (int)((addr & ((1 << (unsigned int)(s + b)) - 1)) >>
                             (unsigned int)b);

        switch (action) {
        case 'L':
            load_cache(tag, setIndex);
            break;

        case 'S':
            store_cache(tag, setIndex);
            break;

        default:
            printf("Invalid action\n");
            exit(1);
        }
    }
    fclose(tfp);
    return parse_error;
}

int main(int argc, char *argv[]) {
    int opt, hflag = 0, vflag = 0, s = -1, b = -1;
    char t[1000];

    // Parse the command line into options
    while ((opt = getopt(argc, argv, "hvs:b:E:t:")) != -1) {
        switch (opt) {
        case 'h':
            hflag = 1;
            break;

        case 'v':
            vflag = 1;
            break;

        case 's':
            s = atoi(optarg);
            break;

        case 'b':
            b = atoi(optarg);
            break;

        case 'E':
            E = atoi(optarg);
            break;

        case 't':
            strcpy(t, optarg);
            break;

        default:
            printf("Error while parsing arguments.\n");
            exit(1);
        }
    }

    // detect whether arguments are not options or values for values
    if (optind < argc) {
        printf("Invalid input\n");
        exit(1);
    }

    // if -h is given, print the help message
    if (hflag) {
        print_help();
        return 0;
    }

    // if -v is given, verbose mode is on
    if (vflag) {
        printf("verbose mode on\n");
    }

    checkValidInput(s, b, E, t);
    init_cache(s, b, E);
    printf("s=%i, E=%i, b=%i\n", s, E, b);
    process_trace_file(t, s, E, b);

    // print the result
    csim_stats_t *stats = malloc(sizeof(csim_stats_t));
    stats->hits = (unsigned long)hit;
    stats->misses = (unsigned long)miss;
    stats->evictions = (unsigned long)eviction;
    stats->dirty_bytes = (unsigned long)(dirtyInCache * B);
    stats->dirty_evictions = (unsigned long)(dirtyEvicted * B);
    printSummary(stats);

    // free memory
    for (int i = 0; i < S; i++) {
        free(cache[i]);
    }
    free(cache);
    free(stats);

    return 0;
}
