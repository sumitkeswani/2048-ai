AI for the [2048 game](http://gabrielecirulli.github.io/2048/). This uses a combination of *Monte Carlo Random runs and expectimax with pruning and evaluation function*, along with a highly-efficient bitboard representation to search upwards of 10 million moves per second on recent hardware. 
Evaluation function includes: Monotonicity, Empty Cells, Merges, High values on corners (Bonuses) and Loss (Punishment).

## Building

### Unix/Linux/OS X

Execute

    ./configure
    make

in a terminal. Any relatively recent C++ compiler should be able to build the output.

Note that you don't do `make install`; this program is meant to be run from this directory.


## Running the command-line version

Run `bin/2048` if you want to see the AI by itself in action.

## Running the browser-control version

### Firefox

Install [Remote Control for Firefox](https://github.com/nneonneo/FF-Remote-Control/raw/V_1.2/remote_control-1.2-fx.xpi).

Open up the [2048 game](http://gabrielecirulli.github.io/2048/) or any compatible clone and start remote control.

Run `2048.py -b firefox` and watch the game!
