#!/usr/bin/env pypy
# -*- coding: utf-8 -*-

from __future__ import print_function
import sys
from itertools import count
from collections import Counter, OrderedDict, namedtuple
from Tkinter import *
import MySQLdb
import atexit

# The table size is the maximum number of elements in the transposition table.
TABLE_SIZE = 1e6

# This constant controls how much time we spend on looking for optimal moves.
NODES_SEARCHED = 1e4

# Mate value must be greater than 8*queen + 2*(rook+knight+bishop)
# King value is set to twice this value such that if the opponent is
# 8 queens up, but we got the king, we still exceed MATE_VALUE.
MATE_VALUE = 30000

# Our board is represented as a 120 character string. The padding allows for
# fast detection of moves that don't stay within the board.
A1, H1, A8, H8 = 91, 98, 21, 28
initial = (
    '         \n'  #   0 -  9
    '         \n'  #  10 - 19
    ' rnbqkbnr\n'  #  20 - 29
    ' pppppppp\n'  #  30 - 39
    ' ........\n'  #  40 - 49
    ' ........\n'  #  50 - 59
    ' ........\n'  #  60 - 69
    ' ........\n'  #  70 - 79
    ' PPPPPPPP\n'  #  80 - 89
    ' RNBQKBNR\n'  #  90 - 99
    '         \n'  # 100 -109
    '          '   # 110 -119
)

###############################################################################
# Move and evaluation tables
###############################################################################

N, E, S, W = -10, 1, 10, -1
directions = {
    'P': (N, 2*N, N+W, N+E),
    'N': (2*N+E, N+2*E, S+2*E, 2*S+E, 2*S+W, S+2*W, N+2*W, 2*N+W),
    'B': (N+E, S+E, S+W, N+W),
    'R': (N, E, S, W),
    'Q': (N, E, S, W, N+E, S+E, S+W, N+W),
    'K': (N, E, S, W, N+E, S+E, S+W, N+W)
}

pst = {
    'P': (0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 198, 198, 198, 198, 198, 198, 198, 198, 0,
        0, 178, 198, 198, 198, 198, 198, 198, 178, 0,
        0, 178, 198, 198, 198, 198, 198, 198, 178, 0,
        0, 178, 198, 208, 218, 218, 208, 198, 178, 0,
        0, 178, 198, 218, 238, 238, 218, 198, 178, 0,
        0, 178, 198, 208, 218, 218, 208, 198, 178, 0,
        0, 178, 198, 198, 198, 198, 198, 198, 178, 0,
        0, 198, 198, 198, 198, 198, 198, 198, 198, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    'B': (
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 797, 824, 817, 808, 808, 817, 824, 797, 0,
        0, 814, 841, 834, 825, 825, 834, 841, 814, 0,
        0, 818, 845, 838, 829, 829, 838, 845, 818, 0,
        0, 824, 851, 844, 835, 835, 844, 851, 824, 0,
        0, 827, 854, 847, 838, 838, 847, 854, 827, 0,
        0, 826, 853, 846, 837, 837, 846, 853, 826, 0,
        0, 817, 844, 837, 828, 828, 837, 844, 817, 0,
        0, 792, 819, 812, 803, 803, 812, 819, 792, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    'N': (0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 627, 762, 786, 798, 798, 786, 762, 627, 0,
        0, 763, 798, 822, 834, 834, 822, 798, 763, 0,
        0, 817, 852, 876, 888, 888, 876, 852, 817, 0,
        0, 797, 832, 856, 868, 868, 856, 832, 797, 0,
        0, 799, 834, 858, 870, 870, 858, 834, 799, 0,
        0, 758, 793, 817, 829, 829, 817, 793, 758, 0,
        0, 739, 774, 798, 810, 810, 798, 774, 739, 0,
        0, 683, 718, 742, 754, 754, 742, 718, 683, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    'R': (0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 1258, 1263, 1268, 1272, 1272, 1268, 1263, 1258, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    'Q': (0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 2529, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
    'K': (0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 60098, 60132, 60073, 60025, 60025, 60073, 60132, 60098, 0,
        0, 60119, 60153, 60094, 60046, 60046, 60094, 60153, 60119, 0,
        0, 60146, 60180, 60121, 60073, 60073, 60121, 60180, 60146, 0,
        0, 60173, 60207, 60148, 60100, 60100, 60148, 60207, 60173, 0,
        0, 60196, 60230, 60171, 60123, 60123, 60171, 60230, 60196, 0,
        0, 60224, 60258, 60199, 60151, 60151, 60199, 60258, 60224, 0,
        0, 60287, 60321, 60262, 60214, 60214, 60262, 60321, 60287, 0,
        0, 60298, 60332, 60273, 60225, 60225, 60273, 60332, 60298, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
}

#depth of analyze human aspect
humanDepth= 0

playerName= "player"

analyzeMode= False
analyzedMoves= []

CENTRAL_FIELDS= [53,54,55,56,57,63,64,65,66,67]
WING_FIELDS= [21,22,27,28,31,32,37,38,41,42,47,48,51,52,57,58,61,62,67,68,71,72,77,78,81,82,87,88,91,92,97,98]
INACTIVE_FIELDS= [91,92,93,94,95,96,97,98]
AGGRESSIVE_FIELDS= [21,22,23,24,25,26,27,28,31,32,33,34,35,36,37,38]
DEFENCE_FIELDS= [81,82,83,84,85,86,87,88,91,92,93,94,95,96,97,98]

# opossites:
# safety king <> active play
# central play <> wing play
# aggressive play <> defence play
central_val= 0
wing_val= 0
active_val= 0
aggressive_val= 0
defence_val= 0
safetyKing_val= 0

def setAnalyzeMode():
    global analyzeMode
    global central_val
    global wing_val
    global active_val
    global aggressive_val
    global defence_val
    global safetyKing_val
    central_val= 1
    wing_val= 1
    active_val= 1
    aggressive_val=1
    defence_val=1
    safetyKing_val=1
    analyzeMode= True

###############################################################################
# Chess logic
###############################################################################

class Position(namedtuple('Position', 'board score wc bc ep kp')):
    """ A state of a chess game
    board -- a 120 char representation of the board
    score -- the board evaluation
    wc -- the castling rights
    bc -- the opponent castling rights
    ep - the en passant square (w przelocie)
    kp - the king passant square ?
    """

    def genMoves(self):
        # For each of our pieces, iterate through each possible 'ray' of moves,
        # as defined in the 'directions' map. The rays are broken e.g. by
        # captures or immediately in case of pieces such as knights.
        for i, p in enumerate(self.board):
            if not p.isupper(): continue
            for d in directions[p]:
                for j in count(i+d, d):
                    q = self.board[j]
                    # Stay inside the board
                    if self.board[j].isspace(): break
                    # Castling
                    if i == A1 and q == 'K' and self.wc[0]: yield (j, j-2)
                    if i == H1 and q == 'K' and self.wc[1]: yield (j, j+2)
                    # No friendly captures
                    if q.isupper(): break
                    # Special pawn stuff
                    if p == 'P' and d in (N+W, N+E) and q == '.' and j not in (self.ep, self.kp): break
                    if p == 'P' and d in (N, 2*N) and q != '.': break
                    if p == 'P' and d == 2*N and (i < A1+N or self.board[i+N] != '.'): break
                    # Move it
                    yield (i, j)
                    # Stop crawlers from sliding dla tych figur brak ciaglych kierunkow
                    if p in ('P', 'N', 'K'): break
                    # No sliding after captures zasloniecie przeciwnik
                    if q.islower(): break

    def rotate(self):
        return Position(
            self.board[::-1].swapcase(), -self.score,
            self.bc, self.wc, 119-self.ep, 119-self.kp)

    def move(self, move):
        i, j = move
        p, q = self.board[i], self.board[j]
        # zdefiniowanie funkcji przemieszczenia figury
        put = lambda board, i, p: board[:i] + p + board[i+1:]
        # Copy variables and reset ep and kp
        board = self.board
        wc, bc, ep, kp = self.wc, self.bc, 0, 0
        score = self.score + self.value(move)
        # Actual move
        board = put(board, j, board[i])
        board = put(board, i, '.')
        # Castling rights
        if i == A1: wc = (False, wc[1])
        if i == H1: wc = (wc[0], False)
        if j == A8: bc = (bc[0], False)
        if j == H8: bc = (False, bc[1])
        # Castling
        if p == 'K':
            wc = (False, False)
            if abs(j-i) == 2:
                kp = (i+j)//2
                board = put(board, A1 if j < i else H1, '.')
                board = put(board, kp, 'R')
        # Special pawn stuff
        if p == 'P':
            if A8 <= j <= H8:
                board = put(board, j, 'Q')
            if j - i == 2*N:
                ep = i + N
            if j - i in (N+W, N+E) and q == '.':
                board = put(board, j+S, '.')
        # We rotate the returned position, so it's ready for the next player
        return Position(board, score, wc, bc, ep, kp).rotate()

    def value(self, move):
        i, j = move
        p, q = self.board[i], self.board[j]
        # Actual move
        score = pst[p][j] - pst[p][i]
        # Capture
        if q.islower():
            score += pst[q.upper()][j]
        # Castling check detection
        if abs(j-self.kp) < 2:
            score += pst['K'][j]
        # Castling
        if p == 'K' and abs(i-j) == 2:
            score += pst['R'][(i+j)//2]
            score -= pst['R'][A1 if j < i else H1]
        # Special pawn stuff
        if p == 'P':
            if A8 <= j <= H8:
                score += pst['Q'][j] - pst['P'][j]
            if j == self.ep:
                score += pst['P'][j+S]
        return score

Entry = namedtuple('Entry', 'depth score gamma move')
tp = OrderedDict()


###############################################################################
# Search logic
###############################################################################

####################
# My added functions
####################

def findPosKing(pos):
    for i, p in enumerate(pos.board):
        if p=='K':
            return i

# analyze human move

def checkIfCentralFields(move):
    return move[1] in CENTRAL_FIELDS

def checkIfWingFields(move):
    return move[1] in WING_FIELDS

def checkIfActiveActiveFields(move,pos):
    return move[0] in INACTIVE_FIELDS and move[1] not in INACTIVE_FIELDS and pos.board[move[0]]!= 'K'

def checkIfAggressivePlay(move,pos):
    if move[1] in AGGRESSIVE_FIELDS:
        return True
    aggressive_parameter= 0
    p= pos.board[move[0]]
    for d in directions[p]:
        for j in count(move[1]+d, d):
            q= pos.board[j]
            if pos.board[j].isspace(): break
            if q.isupper():
                aggressive_parameter-=0.5
                break
            if q.islower():
                aggressive_parameter+=0.6
                if q=='k':
                    aggressive_parameter+=1
                break
            if p in ('P', 'N', 'K'): break
    if aggressive_parameter>0:
        return True
    else:
        return False

def checkIfDefensivePlay(move):
    return move[1] in DEFENCE_FIELDS

def checkIfSafetyKing(move,pos):
    safety_parameter=0
    kingPos= findPosKing(pos)
    if move[0] in [kingPos+N,kingPos+N+E,kingPos+N+W] and move[1] not in [kingPos+N,kingPos+N+E,kingPos+N+W]:
        safety_parameter-= 0.5
    if move[1] in [kingPos+N,kingPos+N+E,kingPos+N+W]:
        safety_parameter+= 0.6
    if move[0]==kingPos:
        defenceCounter=0
        if move[0] in DEFENCE_FIELDS:
            if pos.board[move[0]+N].isupper:
                defenceCounter-=1
            if pos.board[move[0]+N+E].isupper:
                defenceCounter-=1
            if pos.board[move[0]+N+W].isupper:
                defenceCounter-=1
            if pos.board[move[1]+N].isupper:
                defenceCounter+=1
            if pos.board[move[1]+N+E].isupper:
                defenceCounter+=1
            if pos.board[move[1]+N+W].isupper:
                defenceCounter+=1
            safety_parameter+=0.8*defenceCounter
    if safety_parameter>0:
        return True
    else:
        return False
#############################################################

# computer decision

def analyzeCentralFields(move):
    if analyzeMode:
        val_factor= central_val
    else:
        val_factor= wing_val
    score=0
    if move[1] in CENTRAL_FIELDS:
        score+=0.3 * val_factor
    return score

def analyzeWingFields(move):
    if analyzeMode:
        val_factor= wing_val
    else:
        val_factor= central_val
    score=0
    if move[1] in WING_FIELDS:
        score+=0.3*val_factor
    return score

def analyzeActiveActiveFields(move,pos):
    if analyzeMode:
        val_factor= active_val
    else:
        val_factor= safetyKing_val
    score=0
    if move[0] in INACTIVE_FIELDS and move[1] not in INACTIVE_FIELDS and pos.board[move[0]]!= 'K':
        score+=0.3 * val_factor
    return score

def analyzeAggressivePlay(move,pos):
    if analyzeMode:
        val_factor= aggressive_val
        val_oppossite= defence_val
    else:
        val_factor= defence_val
        val_oppossite= aggressive_val
    score=0
    if move[1] in AGGRESSIVE_FIELDS:
        score+= 0.25*val_factor
    p= pos.board[move[0]]
    for d in directions[p]:
        for j in count(move[1]+d, d):
            q= pos.board[j]
            if pos.board[j].isspace(): break
            if q.isupper():
                score-= 0.05*val_oppossite
                break
            if q.islower():
                score+=0.05*val_factor
                if q=='k':
                    score+=0.3*val_factor
                break
            if p in ('P', 'N', 'K'): break
    return score

def analyzeDefensivePlay(move):
    if analyzeMode:
        val_factor= defence_val
    else:
        val_factor= aggressive_val
    score=0
    if move[1] in DEFENCE_FIELDS:
        score+= 0.3*val_factor
    return score

def analyzeSafetyKing(move,pos):
    if analyzeMode:
        val_factor= safetyKing_val
    else:
        val_factor= active_val
    score=0
    kingPos= findPosKing(pos)
    if move[0] in [kingPos+N,kingPos+N+E,kingPos+N+W] and move[1] not in [kingPos+N,kingPos+N+E,kingPos+N+W]:
        score-= 0.3*val_factor
    if move[1] in [kingPos+N,kingPos+N+E,kingPos+N+W]:
        score+= 0.3*val_factor
    if move[0]==kingPos:
        defenceCounter=0
        if move[0] in DEFENCE_FIELDS:
            if pos.board[move[0]+N].isupper:
                defenceCounter-=1
            if pos.board[move[0]+N+E].isupper:
                defenceCounter-=1
            if pos.board[move[0]+N+W].isupper:
                defenceCounter-=1
            if pos.board[move[1]+N].isupper:
                defenceCounter+=1
            if pos.board[move[1]+N+E].isupper:
                defenceCounter+=1
            if pos.board[move[1]+N+W].isupper:
                defenceCounter+=1
            score+= 0.3*val_factor*defenceCounter
    return score
#############################################################################

def normalizeParameters():
    global central_val
    global wing_val
    global active_val
    global aggressive_val
    global defence_val
    global safetyKing_val
    if central_val<0:
        central_val=0
    if wing_val<0:
        wing_val=0
    if active_val<0:
        active_val=0
    if aggressive_val<0:
        aggressive_val=0
    if defence_val<0:
        defence_val=0
    if safetyKing_val<0:
        safetyKing_val=0

def analyzeHumansMove(move,pos):
    global central_val
    central_val+= 1 if checkIfCentralFields(move)>0 else -0.4
    global wing_val
    wing_val+= 1 if checkIfWingFields(move)>0 else -0.4
    global active_val
    active_val+= 1 if checkIfActiveActiveFields(move,pos)>0 else -0.4
    global aggressive_val
    aggressive_val+= 1 if checkIfAggressivePlay(move,pos)>0 else -0.5
    global defence_val
    defence_val+= 1 if checkIfDefensivePlay(move)>0 else -0.4
    global safetyKing_val
    safetyKing_val+= 1 if checkIfSafetyKing(move,pos)>0 else -0.4

    normalizeParameters()

def obtainMove(move,pos):
    scoreShift=0
    #central play
    scoreShift+= analyzeCentralFields(move)
    #wing play
    scoreShift+= analyzeWingFields(move)
    #tempo mobility
    scoreShift+= analyzeActiveActiveFields(move,pos)
    #aggressive
    scoreShift+= analyzeAggressivePlay(move,pos)
    #defensive
    scoreShift+= analyzeDefensivePlay(move)
    #king safety
    scoreShift+= analyzeSafetyKing(move,pos)

    return scoreShift
#############################################

nodes = 0
def bound(pos, gamma, depth):
    """ returns s(pos) <= r < gamma    if s(pos) < gamma
        returns s(pos) >= r >= gamma   if s(pos) >= gamma """
    global nodes; nodes += 1

    # Look in the table if we have already searched this position before.
    # We use the table value if it was done with at least as deep a search
    # as ours, and the gamma value is compatible.
    entry = tp.get(pos)
    if entry is not None and entry.depth >= depth and (
            entry.score < entry.gamma and entry.score < gamma or
            entry.score >= entry.gamma and entry.score >= gamma):
        return entry.score

    # Stop searching if we have won/lost.
    if abs(pos.score) >= MATE_VALUE:
        return pos.score

    # Null move. Is also used for stalemate checking
    nullscore = -bound(pos.rotate(), 1-gamma, depth-3) if depth > 0 else pos.score
    #nullscore = -MATE_VALUE*3 if depth > 0 else pos.score
    if nullscore >= gamma:
        return nullscore

    # We generate all possible, pseudo legal moves and order them to provoke
    # cuts. At the next level of the tree we are going to minimize the score.
    # This can be shown equal to maximizing the negative score, with a slightly
    # adjusted gamma value.
    best, bmove = -3*MATE_VALUE, None
    for move in sorted(pos.genMoves(), key=pos.value, reverse=True):
        # We check captures with the value function, as it also contains ep and kp
        if depth <= 0 and pos.value(move) < 150:
            break

        addedScore= obtainMove(move,pos) if depth>humanDepth else 0

        score = -bound(pos.move(move), 1-gamma, depth-1) +addedScore
        if score > best:
            best = score
            bmove = move
        if score >= gamma:
            break

    # If there are no captures, or just not any good ones, stand pat
    if depth <= 0 and best < nullscore:
        return nullscore
    # Check for stalemate. If best move loses king, but not doing anything
    # would save us. Not at all a perfect check.
    if depth > 0 and best <= -MATE_VALUE is None and nullscore > -MATE_VALUE:
        best = 0

    # We save the found move together with the score, so we can retrieve it in
    # the play loop. We also trim the transposition table in FILO order.
    # We prefer fail-high moves, as they are the ones we can build our pv from.
    if entry is None or depth >= entry.depth and best >= gamma:
        tp[pos] = Entry(depth, best, gamma, bmove)
        if len(tp) > TABLE_SIZE:
            tp.pop()
    return best


def search(pos, maxn=NODES_SEARCHED):
    """ Iterative deepening MTD-bi search """
    global nodes; nodes = 0

    # We limit the depth to some constant, so we don't get a stack overflow in
    # the end game.
    for depth in range(1, 99):
        global humanDepth
        humanDepth= depth-3
        # The inner loop is a binary search on the score of the position.
        # Inv: lower <= score <= upper
        # However this may be broken by values from the transposition table,
        # as they don't have the same concept of p(score). Hence we just use
        # 'lower < upper - margin' as the loop condition.
        lower, upper = -3*MATE_VALUE, 3*MATE_VALUE

        while lower < upper - 3:
            gamma = (lower+upper+1)//2
            score = bound(pos, gamma, depth)
            if score >= gamma:
                lower = score
            if score < gamma:
                upper = score

        print("Searched %d nodes. Depth %d. Score %d(%d/%d)" % (nodes, depth, score, lower, upper))
        if analyzeMode:
            new_move= tp.get(pos).move
            for i, (t1,t2) in enumerate(analyzedMoves):
                if t1==new_move:
                    del analyzedMoves[i]
            analyzedMoves.append((new_move,score))

        # We stop deepening if the global N counter shows we have spent too
        # long, or if we have already won the game.
        if nodes >= maxn or abs(score) >= MATE_VALUE:
            break

    # If the game hasn't finished we can retrieve our move from the
    # transposition table.
    entry = tp.get(pos)
    if entry is not None:
        return entry.move, score
    return None, score


###############################################################################
# Database Logic
###############################################################################

def fillFactorsFromDatabase(player):
    global central_val
    global wing_val
    global active_val
    global aggressive_val
    global defence_val
    global safetyKing_val
    central_val= player[2]
    wing_val= player[3]
    active_val=player[4]
    aggressive_val=player[5]
    defence_val=player[6]
    safetyKing_val=player[7]

def initDatabaseAndCheckPlayer(name):
    try:
        db = MySQLdb.connect(host="localhost",user="root",passwd="0501",db="sunfish_database")
        with db:
            cur = db.cursor()
           # cur.execute("DROP TABLE IF EXISTS Players")
         #   cur.execute("CREATE TABLE Players(Id INT PRIMARY KEY AUTO_INCREMENT, Name VARCHAR(25), centralValue DOUBLE,"
         #      "wingValue DOUBLE, activeValue DOUBLE , aggressiveValue DOUBLE , defenceValue DOUBLE , safetyKingValue DOUBLE )")
            # check for player
            cur.execute("SELECT * FROM Players WHERE Name=%s",name)
            player = cur.fetchone()
            if player is None:
                cur.execute("INSERT INTO Players(Name,centralValue,wingValue,activeValue,aggressiveValue,defenceValue,"
                            "safetyKingValue) VALUES(%s,0,0,0,0,0,0)",name)
            else:
                fillFactorsFromDatabase(player)
            global playerName
            playerName= name
    except MySQLdb.Error, e:
        print("Error %d: %s" % (e.args[0],e.args[1 ]))
        sys.exit(1)
    finally:
        if db:
            db.close()

@atexit.register
def savePlayerIntoDatabase():
    try:
        db = MySQLdb.connect(host="localhost",user="root",passwd="0501",db="sunfish_database")
        with db:
            cur= db.cursor()
            cur.execute("UPDATE Players SET centralValue= %s, wingValue= %s, activeValue= %s, aggressiveValue= %s, "
                        "defenceValue= %s, safetyKingValue= %s WHERE name= %s",(central_val,wing_val,
                        active_val,aggressive_val,defence_val,safetyKing_val,playerName))
    except MySQLdb.Error, e:
        print("Error %d: %s" % (e.args[0],e.args[1]))
        sys.exit(1)
    finally:
        if db:
            db.close()

###############################################################################
# User interface
###############################################################################

# Python 2 compatability
if sys.version_info[0] == 2:
    input = raw_input


def parse(c):
    fil, rank = ord(c[0]) - ord('a'), int(c[1]) - 1
    return A1 + fil - 10*rank


def render(i):
    rank, fil = divmod(i - A1, 10)
    return chr(fil + ord('a')) + str(-rank + 1)

def encode(i):
    move0= H1-(i[0]-A8)
    move1= H1-(i[1]-A8)
    return move0, move1


def defenceScale(val):
    global defence_val
    defence_val= float(val)

def centralScale(val):
    global central_val
    central_val= float(val)

def wingScale(val):
    global wing_val
    wing_val= float(val)

def activeScale(val):
    global active_val
    active_val= float(val)

def aggressiveScale(val):
    global aggressive_val
    aggressive_val= float(val)

def safetyKingScale(val):
    global safetyKing_val
    safetyKing_val= float(val)

def prepareScaleGui():
    master = Tk()

    frame = Frame(master)
    frame.pack()

    bottomframe = Frame(master)
    bottomframe.pack( side = BOTTOM )

    endframe= Frame(master)
    endframe.pack( side = BOTTOM )

    w1 = Scale(frame, from_=0, to=6, label="aggressive", fg="Blue", resolution=0.1, command=aggressiveScale)
    w2 = Scale(frame, from_=0, to=6, label="defence", fg="Red", resolution=0.1, command=defenceScale)
    w3 = Scale(bottomframe, from_=0, to=6, label="centrality", fg="Blue", resolution=0.1, command=centralScale)
    w4 = Scale(bottomframe, from_=0, to=6, label="wings", fg="Red", resolution=0.1, command=wingScale)
    w5 = Scale(endframe, from_=0, to=6, label="activity", fg="Blue", resolution=0.1, command=activeScale)
    w6 = Scale(endframe, from_=0, to=6, label="safety", fg="Red", resolution=0.1, command=safetyKingScale)
    w1.pack(side= LEFT)
    w2.pack(side= LEFT)
    w3.pack(side= LEFT)
    w4.pack(side= LEFT)
    w5.pack(side= LEFT)
    w6.pack(side= LEFT)

def main():
    pos = Position(initial, 0, (True,True), (True,True), 0, 0)

    if sys.argv.__len__() < 2:
        print("Usage: python sunfish [player name]")
        exit()
    if sys.argv.__len__()==3:
        if sys.argv[2]=="analyze":
            global analyzeMode
            analyzeMode= True
            prepareScaleGui()
        else:
            print("Usage: python sunfish [player name] analyze")
            exit()

    initDatabaseAndCheckPlayer(sys.argv[1])

    while True:
        # We add some spaces to the board before we print it.
        # That makes it more readable and pleasing.
        print(' '.join(pos.board))

        # We query the user until she enters a legal move.
        move = None
        while move not in pos.genMoves():
            crdn = input("Your move: ")
            try:
              move = parse(crdn[0:2]), parse(crdn[2:4])
            except ValueError:
              # Inform the user when invalid input (e.g. "help") is entered
              print("Invalid input. Please enter a move in the proper format (e.g. g8f6)")

        # check style and save to database
        if analyzeMode==False :
            analyzeHumansMove(move,pos)

        pos = pos.move(move)
        print("ATRYBUTY PO RUCHU: ")
        print("CENTRAL_VAL: " +str(central_val))
        print("WING_VAL: " +str(wing_val))
        print("AGGRESSIVE_VAL: " +str(aggressive_val))
        print("DEFENCE_VAL: " +str(defence_val))
        print("ACTIVE_VAL: " +str(active_val))
        print("SAFETYKING_VAL: " +str(safetyKing_val))
        # After our move we rotate the board and print it again.
        # This allows us to see the effect of our move.
        print(' '.join(pos.rotate().board))

        # Fire up the engine to look for a move.
        move, score = search(pos)
        if score <= -MATE_VALUE:
            print("You won")
            break
        if score >= MATE_VALUE:
            print("You lost")
            break

        # The black player moves from a rotated position, so we have to
        # 'back rotate' the move before printing it.
        print("Actual score: ", score)
        print("My move:", render(119-move[0]) + render(119-move[1]))
        if analyzeMode==False:
            pos = pos.move(move)
        else:
            for i, (t1, t2) in enumerate(analyzedMoves):
                if t1 == move:
                    del analyzedMoves[i]
            if len(analyzedMoves)>0:
                print("Other analyzed moves:")
                for move,score in analyzedMoves:
                    print("Move: "+render(119-move[0]) + render(119-move[1])+" , Score: "+str(score))

            move = None
            while move not in pos.genMoves():
                crdn = input("Opponent move: ")
                try:
                    move = parse(crdn[0:2]), parse(crdn[2:4])
                    move= encode(move)
                except ValueError:
                    print("Invalid input. Please enter a move in the proper format (e.g. g8f6)")
            pos = pos.move(move)
if __name__ == '__main__':
    main()
