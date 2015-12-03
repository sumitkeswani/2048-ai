#include <ctype.h>
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <cmath>
#include <algorithm>
#include <bits/stdc++.h>
#include "2048.h"

#include "config.h"
#if defined(HAVE_UNORDERED_MAP)
    #include <unordered_map>
    typedef std::unordered_map<board_t, float> trans_table_t;
#elif defined(HAVE_TR1_UNORDERED_MAP)
    #include <tr1/unordered_map>
    typedef std::tr1::unordered_map<board_t, float> trans_table_t;
#else
    #include <map>
    typedef std::map<board_t, float> trans_table_t;
#endif

/* MSVC compatibility: undefine max and min macros */
#if defined(max)
#undef max
#endif

#if defined(min)
#undef min
#endif

#define DEPTH 13
#define OPEN_CELLS 7
#define MONOTONICITY_WEIGHT 47
#define POTENTIAL_MERGES_WEIGHT 200
#define CURRENT_MERGES_WEIGHT  400
#define OPEN_CELLS_WEIGHT 270

int getExpectedValue(board_t board, int depth);


static inline board_t transpose(board_t x)
{
	board_t a1 = x & 0xF0F00F0FF0F00F0FULL;
	board_t a2 = x & 0x0000F0F00000F0F0ULL;
	board_t a3 = x & 0x0F0F00000F0F0000ULL;
	board_t a = a1 | (a2 << 12) | (a3 >> 12);
	board_t b1 = a & 0xFF00FF0000FF00FFULL;
	board_t b2 = a & 0x00FF00FF00000000ULL;
	board_t b3 = a & 0x00000000FF00FF00ULL;
	return b1 | (b2 >> 24) | (b3 << 24);
}

// Count the number of empty positions (= zero nibbles) in a board.
// Precondition: the board cannot be fully empty.
static int count_empty(uint64_t x)
{
	x |= (x >> 2) & 0x3333333333333333ULL;
	x |= (x >> 1);
	x = ~x & 0x1111111111111111ULL;

	x += x >> 32;
	x += x >> 16;
	x += x >>  8;
	x += x >>  4; // this can overflow to the next nibble if there were 16 empty positions
	return x & 0xf;
}

/* We can perform state lookups one row at a time by using arrays with 65536 entries. */

/* Move tables. Each row or compressed column is mapped to (oldrow^newrow) assuming row/col 0.
 *
 * Thus, the value is 0 if there is no move, and otherwise equals a value that can easily be
 * xor'ed into the current board state to update the board. */
static row_t row_left_table [65536];
static row_t row_right_table[65536];
static board_t col_up_table[65536];
static board_t col_down_table[65536];
static float heur_score_table[65536];
static float score_table[65536];

void init_tables() {
    for (unsigned row = 0; row < 65536; ++row) {
        unsigned line[4] = {
                (row >>  0) & 0xf,
                (row >>  4) & 0xf,
                (row >>  8) & 0xf,
                (row >> 12) & 0xf
        };

        float heur_score = 0.0f;
        float score = 0.0f;
        for (int i = 0; i < 4; ++i) {
            int rank = line[i];
            if (rank == 0) {
                heur_score += 10000.0f;
            } else if (rank >= 2) {
                // the score is the total sum of the tile and all intermediate merged tiles
                score += (rank - 1) * (1 << rank);
            }
        }
        score_table[row] = score;

        int maxi = 0;
        for (int i = 1; i < 4; ++i) {
            if (line[i] > line[maxi]) maxi = i;
        }

        if (maxi == 0 || maxi == 3) heur_score += 20000.0f;

        // Check if maxi's are close to each other, and of diff ranks (eg 128 256)
        for (int i = 1; i < 4; ++i) {
            if ((line[i] == line[i - 1] + 1) || (line[i] == line[i - 1] - 1)) heur_score += 1000.0f;
        }

        // Check if the values are ordered:
        if ((line[0] < line[1]) && (line[1] < line[2]) && (line[2] < line[3])) heur_score += 10000.0f;
        if ((line[0] > line[1]) && (line[1] > line[2]) && (line[2] > line[3])) heur_score += 10000.0f;

        heur_score_table[row] = heur_score;


        // execute a move to the left
        for (int i = 0; i < 3; ++i) {
            int j;
            for (j = i + 1; j < 4; ++j) {
                if (line[j] != 0) break;
            }
            if (j == 4) break; // no more tiles to the right

            if (line[i] == 0) {
                line[i] = line[j];
                line[j] = 0;
                i--; // retry this entry
            } else if (line[i] == line[j] && line[i] != 0xf) {
                line[i]++;
                line[j] = 0;
            }
        }

        row_t result = (line[0] <<  0) |
                       (line[1] <<  4) |
                       (line[2] <<  8) |
                       (line[3] << 12);
        row_t rev_result = reverse_row(result);
        unsigned rev_row = reverse_row(row);

        row_left_table [    row] =                row  ^                result;
        row_right_table[rev_row] =            rev_row  ^            rev_result;
        col_up_table   [    row] = unpack_col(    row) ^ unpack_col(    result);
        col_down_table [rev_row] = unpack_col(rev_row) ^ unpack_col(rev_result);
    }
}

static inline board_t execute_move_0(board_t board) {
    board_t ret = board;
    board_t t = transpose(board);
    ret ^= col_up_table[(t >>  0) & ROW_MASK] <<  0;
    ret ^= col_up_table[(t >> 16) & ROW_MASK] <<  4;
    ret ^= col_up_table[(t >> 32) & ROW_MASK] <<  8;
    ret ^= col_up_table[(t >> 48) & ROW_MASK] << 12;
    return ret;
}

static inline board_t execute_move_1(board_t board) {
    board_t ret = board;
    board_t t = transpose(board);
    ret ^= col_down_table[(t >>  0) & ROW_MASK] <<  0;
    ret ^= col_down_table[(t >> 16) & ROW_MASK] <<  4;
    ret ^= col_down_table[(t >> 32) & ROW_MASK] <<  8;
    ret ^= col_down_table[(t >> 48) & ROW_MASK] << 12;
    return ret;
}

static inline board_t execute_move_2(board_t board) {
    board_t ret = board;
    ret ^= board_t(row_left_table[(board >>  0) & ROW_MASK]) <<  0;
    ret ^= board_t(row_left_table[(board >> 16) & ROW_MASK]) << 16;
    ret ^= board_t(row_left_table[(board >> 32) & ROW_MASK]) << 32;
    ret ^= board_t(row_left_table[(board >> 48) & ROW_MASK]) << 48;
    return ret;
}

static inline board_t execute_move_3(board_t board) {
    board_t ret = board;
    ret ^= board_t(row_right_table[(board >>  0) & ROW_MASK]) <<  0;
    ret ^= board_t(row_right_table[(board >> 16) & ROW_MASK]) << 16;
    ret ^= board_t(row_right_table[(board >> 32) & ROW_MASK]) << 32;
    ret ^= board_t(row_right_table[(board >> 48) & ROW_MASK]) << 48;
    return ret;
}

/* Execute a move. */
static inline board_t execute_move(int move, board_t board) {
    switch(move) {
    case 0: // up
        return execute_move_0(board);
    case 1: // down
        return execute_move_1(board);
    case 2: // left
        return execute_move_2(board);
    case 3: // right
        return execute_move_3(board);
    default:
        return ~0ULL;
    }
}

static inline int get_max_rank(board_t board) {
    int maxrank = 0;
    while (board) {
        maxrank = std::max(maxrank, int(board & 0xf));
        board >>= 4;
    }
    return maxrank;
}

struct eval_state {
    trans_table_t trans_table; 
    float cprob_thresh;
    int maxdepth;
    int curdepth;
    int cachehits;
    int moves_evaled;

    eval_state() : cprob_thresh(0), maxdepth(0), curdepth(0), cachehits(0), moves_evaled(0) {
    }
};

// score a single board heuristically
static float score_heur_board(board_t board);
// score a single board actually (adding in the score from spawned 4 tiles)
static float score_board(board_t board);
// score over all possible moves
static float score_move_node(eval_state &state, board_t board, float cprob);
// score over all possible tile choices and placements
static float score_tilechoose_node(eval_state &state, board_t board, float cprob);


static float score_helper(board_t board, const float* table) {
    return table[(board >>  0) & ROW_MASK] +
           table[(board >> 16) & ROW_MASK] +
           table[(board >> 32) & ROW_MASK] +
           table[(board >> 48) & ROW_MASK];
}

static float score_heur_board(board_t board) {
    return score_helper(board , heur_score_table) + score_helper(transpose(board), heur_score_table) + 100000.0f;
}

static float score_board(board_t board) {
    return score_helper(board, score_table);
}

static float score_tilechoose_node(eval_state &state, board_t board, float cprob) {
    int num_open = count_empty(board);
    cprob /= num_open;

    float res = 0.0f;
    board_t tmp = board;
    board_t tile_2 = 1;
    while (tile_2) {
        if ((tmp & 0xf) == 0) {
            res += score_move_node(state, board |  tile_2      , cprob * 0.9f) * 0.9f;
            res += score_move_node(state, board | (tile_2 << 1), cprob * 0.1f) * 0.1f;
        }
        tmp >>= 4;
        tile_2 <<= 4;
    }
    return res / num_open;
}

// Statistics and controls
// cprob: cumulative probability
// don't recurse into a node with a cprob less than this threshold
static const float CPROB_THRESH_BASE = 0.0001f;
static const int CACHE_DEPTH_LIMIT  = 6;
static const int SEARCH_DEPTH_LIMIT = 8;

static float score_move_node(eval_state &state, board_t board, float cprob) {
    if (cprob < state.cprob_thresh || state.curdepth >= SEARCH_DEPTH_LIMIT) {
        if(state.curdepth > state.maxdepth)
            state.maxdepth = state.curdepth;
        return score_heur_board(board);
    }

    if(state.curdepth < CACHE_DEPTH_LIMIT) {
        const trans_table_t::iterator &i = state.trans_table.find(board);
        if(i != state.trans_table.end()) {
            state.cachehits++;
            return i->second;
        }
    }

    float best = 0.0f;
    state.curdepth++;
    for (int move = 0; move < 4; ++move) {
        board_t newboard = execute_move(move, board);
        state.moves_evaled++;

        if (board != newboard) {
            best = std::max(best, score_tilechoose_node(state, newboard, cprob));
        }
    }
    state.curdepth--;

    if (state.curdepth < CACHE_DEPTH_LIMIT) {
        state.trans_table[board] = best;
    }

    return best;
}

static float _score_toplevel_move(eval_state &state, board_t board, int move) {
    //int maxrank = get_max_rank(board);
    board_t newboard = execute_move(move, board);

    if(board == newboard)
        return 0;

    state.cprob_thresh = CPROB_THRESH_BASE;

    return score_tilechoose_node(state, newboard, 1.0f) + 1e-6;
}

float score_toplevel_move(board_t board, int move) {
    float res;
    struct timeval start, finish;
    double elapsed;
    eval_state state;

    gettimeofday(&start, NULL);
    res = _score_toplevel_move(state, board, move);
    gettimeofday(&finish, NULL);

    elapsed = (finish.tv_sec - start.tv_sec);
    elapsed += (finish.tv_usec - start.tv_usec) / 1000000.0;


    return res;
}



/* Find the best move for a given board. */
int find_best_move_original(board_t board) {
    int move;
    float best = 0;
    int bestmove = -1;

    print_board(board);

    for(move=0; move<4; move++) {
        float res = score_toplevel_move(board, move);

        if(res > best) {
            best = res;
            bestmove = move;
        }
    }

    return bestmove;
}

int ask_for_move(board_t board) {
    int move;
    char validstr[5];
    char *validpos = validstr;

    print_board(board);

    for(move=0; move<4; move++) {
        if(execute_move(move, board) != board)
            *validpos++ = "UDLR"[move];
    }
    *validpos = 0;
    if(validpos == validstr)
        return -1;

    while(1) {
        char movestr[64];
        const char *allmoves = "UDLR";



        if(!fgets(movestr, sizeof(movestr)-1, stdin))
            return -1;

        if(!strchr(validstr, toupper(movestr[0]))) {
            printf("Invalid move.\n");
            continue;
        }

        return strchr(allmoves, toupper(movestr[0])) - allmoves;
    }
}


static board_t draw_tile() {
    return (unif_random(10) < 9) ? 1 : 2;
}

static board_t insert_tile_rand(board_t board, board_t tile) {
    int index = unif_random(count_empty(board));
    board_t tmp = board;
    while (true) {
        while ((tmp & 0xf) != 0) {
            tmp >>= 4;
            tile <<= 4;
        }
        if (index == 0) break;
        --index;
        tmp >>= 4;
        tile <<= 4;
    }
    return board | tile;
}


static board_t initial_board() {
    board_t board = draw_tile() << (4 * unif_random(16));
    return insert_tile_rand(board, draw_tile());
}




//******************************************************************************************
//Evaluation Functions starts.

int noOfOpenCells(board_t board)
{
    int count = 0;
    for(int i=0;i<16;i++)
    {
        int x = (board & 0xf);
        board >>= 4;
        if(x == 0)
        {
            count++;
        }
    }
    return count;
}

int rowMonotonicity(uint64_t board)
{
    int ans = 0;
    for(int i=0;i<4;i++)
    {
        int flag = 0;
        int last = -1;
        for(int j=0;j<4;j++)
        {
            if((board & 0xf) >= last)
            {
                last = board & 0xf;
                board >>= 4;
            }
            else
            {
                flag = -1;
                break;
            }
        }
        if(flag == 0)
            ans++;
        else
        {
            flag = 0;
            last = 20;
            for(int j=0;j<4;j++)
            {
                if((board & 0xf) <= last)
                {
                    last = board & 0xf;
                    board >>= 4;
                }
                else
                {
                    flag = -1;
                    break;
                }
            }
            if(flag == 0)
                ans++;
        }
        
    }

    return ans;
}

int minVal(int a, int b)
{
	return (a<b)? a: b;
}

int monotonicity(uint64_t board)
{
    return minVal(rowMonotonicity(board), rowMonotonicity(transpose(board)));
}

int potentialMerges(board_t board)
{
    int maxPotential = -1;
    for(int move=0;move<4;move++)
    {
        board_t tempBoard = execute_move(move, board);
        int pot = noOfOpenCells(tempBoard) - noOfOpenCells(board);
        if(pot > maxPotential)
        {
            maxPotential = pot;
        }
    }

    return maxPotential;
}

int currentMerges(board_t board, board_t origBoard)
{
    //Returns no of open cells now - before
    int ans = noOfOpenCells(board) - noOfOpenCells(origBoard);
    return ans;
}

int lostPenalty(board_t board)
{
    int move;
    for(move = 0; move < 4; move++) {
        if(execute_move(move, board) != board)
        {
            break;
        }
    }
    if(move == 4)
        return 20000000;

    return 0;
}



//These weights are cconsidered from nneonneo's 2048 AI.
//who has done meta optimization using CMA-ES
//Reference: http://stackoverflow.com/questions/22342854/what-is-the-optimal-algorithm-for-the-game-2048
int evaluateBoard(board_t board, board_t origBoard)
{
    return  MONOTONICITY_WEIGHT * monotonicity(board)+
            POTENTIAL_MERGES_WEIGHT * potentialMerges(board)+
            CURRENT_MERGES_WEIGHT * currentMerges(board, origBoard)+
            OPEN_CELLS_WEIGHT * noOfOpenCells(board)-
            lostPenalty(board);
}

board_t insertTile(board_t board, int index)
{
	board_t x = 1;
	for(int i=0;i<index;i++)
	{
		x <<= 4;
	}
	return (board | x);
}

board_t insertTile(board_t board, int index, int input)
{
	board_t x;
	if(input == 1)	x = 0x1;
	else 			x = 2;

	for(int i=0;i<index;i++)
	{
		x <<= 4;
	}
	return (board | x);
}



//Indirect recursive functions that call each other for
//the 2 types of nodes we have -> chance node and state node.


//Function for chance node
int getExpectedValue1(board_t board, int depth)
{
	int move;
    board_t tempBoard[4];
    int max_value = -1;
    int moveValue[4];

    for(move = 0; move < 4; move++) {
        if(execute_move(move, board) != board)
            break;
    }
    if(move == 4)
    	return 0;

	for(move=0;move<4;move++)
    {
        tempBoard[move] = execute_move(move, board);
        moveValue[move] = evaluateBoard(tempBoard[move], board);
        if(max_value < moveValue[move])
        {
            max_value = moveValue[move];
        }
    }

    if(depth == 0)
    {
        return max_value;
    }

    int maxExpectation;
    for(move = 0;move < 4;move++)
    {
        maxExpectation = INT_MIN;

        if((tempBoard[move] != board) && (moveValue[move] >= max_value/2))           //Pruning threshold
        {
            int expectedValue = getExpectedValue(tempBoard[move], depth-1);
            if(expectedValue > maxExpectation)
            {
                maxExpectation = expectedValue;
            }
        }
    }

    return maxExpectation;

}

//Function for state node
int getExpectedValue(board_t board, int depth)
{
	if(depth == 0)
	{
		board_t tempBoard = board;

		int twoTile = 0;
		int fourTile = 0;
		int num = 0;

		for(int i=0;i<16;i++)
		{
			if(tempBoard & 0xf == 0)
			{
				num++;
				twoTile += getExpectedValue1(insertTile(board, i, 1), depth-1);
				fourTile += getExpectedValue1(insertTile(board, i, 2), depth-1);
			}

			tempBoard >>= 4;
		}

		int ans = (int)(0.9*(twoTile/num) + 0.1*(fourTile/num));
		return ans;
	}
	
}
//




void play_game(get_move_func_t get_move) {
    board_t board = initial_board();
    int moveno = 0;
    int scorepenalty = 0; // "penalty" for obtaining free 4 tiles

    while(1)
    {
        if(noOfOpenCells(board) > OPEN_CELLS)          //This would have a branching factor for 2*OPEN_CELLS = 14 for now     
        {												//because of possibilities of occurance of 2 and 4 in each cells
            int move;
            board_t tempBoard[4];
            int max_value = -1;
            int moveValue[4];
            int finalMove = -1;
            board_t newBoard;

            for(move = 0; move < 4; move++) {
                if(execute_move(move, board) != board)
                    break;
            }
            if(move == 4)
                break; // no legal moves



            for(move=0;move<4;move++)
            {
                tempBoard[move] = execute_move(move, board);
                moveValue[move] = evaluateBoard(tempBoard[move], board);
                if(max_value < moveValue[move])
                {
                    max_value = moveValue[move];
                }
            }

            for(move = 0;move < 4;move++)
            {
                int maxExpectation = INT_MIN;

                if((tempBoard[move] != board) && (moveValue[move] >= max_value/2))           //Pruning threshold->half the max value 
                {
                    int expectedValue = getExpectedValue(tempBoard[move], DEPTH);
                    if(expectedValue > maxExpectation)
                    {
                        maxExpectation = expectedValue;
                        finalMove = move;
                    }
                }
            }

            //finalMove has the value which is going to be taken after this step!!
            if(move < 0)
                break;

            newBoard = tempBoard[finalMove];
            if(newBoard == board)
            {
                printf("Illegal move!\n");
                moveno--;
                continue;
            }

            board_t tile = draw_tile();
            if (tile == 2) scorepenalty += 4;
            board = insert_tile_rand(newBoard, tile);

        }
        else                   //Random runnign algo.
        {
            int move;
            board_t newboard;

            for(move = 0; move < 4; move++) {
                if(execute_move(move, board) != board)
                    break;
            }
            if(move == 4)
                break; // no legal moves


            move = get_move(board);
            if(move < 0)
                break;

            newboard = execute_move(move, board);
            if(newboard == board) {
                printf("Illegal move!\n");
                moveno--;
                continue;
            }

            board_t tile = draw_tile();
            if (tile == 2) scorepenalty += 4;
            board = insert_tile_rand(newboard, tile);
    	}


    }

	print_board(board);
	printf("\nGame over. Your score is %.0f. The highest rank you achieved was %d.\n", score_board(board) - scorepenalty, get_max_rank(board));
}



//*************************************************************************************
//Random Walk AI
bool movesAvailable(board_t board) {
		int move;
        for(move = 0; move < 4; move++) {
            if(execute_move(move, board) != board)
                break;
        }
        return (move < 4);
}	


bool DEBUG = false;
int RUNS;
time_t startTime;

board_t randomRun(board_t board, int move) {
	board_t orig = board;
	board_t newboard = execute_move(move, board);
	if (newboard == board) {
		return 0;
	}
	board = insert_tile_rand(newboard, draw_tile());



	// run til we can't
	while (true) {
		if (!movesAvailable(board)) break;
		
		if (get_max_rank(board)>get_max_rank(orig)) break; // this is an optimization to run faster. The assumption is that if we created a new max rank all is good again.
		
		board_t newboard = execute_move(unif_random(4), board);
		if (newboard == board) continue;
		board = insert_tile_rand(newboard, draw_tile());
	}
	return board;
}

float MAX;
float MIN;	
int LEVELUP_COUNT;
int ACTUAL_COUNT;
int deepSearch = 0;
int origRuns = 0;

float multiRandomRun(board_t board, int move, int runs) {
	float total = 0.0;
	float max = 0;
	float min = 10000000000;
	board_t max_b, min_b;
	LEVELUP_COUNT = 0;
	ACTUAL_COUNT = 0;
	
	for (int i=0 ; i < runs ; i++) {
		board_t endboard = randomRun(board, move);
		float s = score_board(endboard);

		if (s==0) continue; // illegal move
		ACTUAL_COUNT++;
		
		total += s;
		if (s>max) {
			max = s;
			max_b = endboard;
		}
		if (s<min) {
			min = s;
			min_b = endboard;
		}

		if (get_max_rank(board) < get_max_rank(endboard)) LEVELUP_COUNT++; // count getting a new max rank

	}

	if (ACTUAL_COUNT==0) ACTUAL_COUNT=1; // to avoid dev be 0
	float avg = total / ACTUAL_COUNT;	
	
	MAX = max;
	MIN = min;
	
	return avg; //17

}


int find_best_move_montecarlo(board_t board) {
		float bestScore = 0; 
		int bestMove = -1;
		int bestMoveListInedex = -1;
		float bestMax, bestMin;
		int levelUpCount = 0;
		int actualRuns = 0;
		
		if (origRuns==0) origRuns=RUNS;
		
		if ((deepSearch>0) && (get_max_rank(board) > deepSearch)) {
			deepSearch = 0;
			RUNS = origRuns;

		}

		for (int i=0;i<4;i++) {
			// score move position
			float score = multiRandomRun(board, i, RUNS);
			
			if (score >= bestScore) {
				bestScore = score;
				bestMove = i;
				bestMax = MAX;
				bestMin = MIN;
				levelUpCount = LEVELUP_COUNT;
				actualRuns = ACTUAL_COUNT;
			}
			
			// Deep search. If we touched a new max rank, look deeper because we are close to the critical stages.
			if ((LEVELUP_COUNT > 0) && (get_max_rank(board)>10) && (deepSearch==0)) {
				deepSearch = get_max_rank(board);
				i = 0;
				bestScore = 0;
				RUNS = 1000000;

				continue;
			}
		}
		
		// assert move found		
		if (bestMove == -1) {
			printf("ERROR...");
			exit(1);
		} 

		if (DEBUG) {		
			printf(" (%20llu %20f %d) Chosen move %d ", board, score_board(board), get_max_rank(board), bestMove);
			printf(". [UC %8d|%8d] Search Score %20f | MAX %20f MIN %20f \n", levelUpCount, actualRuns, bestScore, bestMax, bestMin);			
		}
		
		return bestMove;
}

int find_best_move(board_t board) {return find_best_move_montecarlo(board);}

int main(int argc, char **argv) {
    init_tables();


	RUNS = 10000;
	if (argc>1) {
		RUNS = atoi(argv[1]);
	}	
	if (argc>2) {
		DEBUG = true;	
	}
	DEBUG = true;
	
    play_game(find_best_move_montecarlo);
}




#if 0
#endif
