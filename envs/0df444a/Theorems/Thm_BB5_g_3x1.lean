-- Prove2me | Theorems.Thm_BB5_g_3x1
-- name    : BB5.g_3x1
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T14:39:37.889549+00:00
-- url     : https://prove2.me/theorems/21de092e-8337-4e1f-beb8-e05f6d8867ab
-- title:
--   Collatz rule $g(3x+1)\to^{5x^2+25x+27}g(5x+9)$
-- statement:
--   For every $x\in\mathbb{N}$, the five-state champion started in configuration $g(3x+1)$ reaches $g(5x+9)$ after exactly $5x^2+25x+27$ transitions:
--
--   $$g(3x+1)\longrightarrow^{\,5x^2+25x+27\,}g(5x+9).$$
--
--   Here $g(y)$ is the configuration with the machine in state $A$, its head on the blank cell immediately to the left of a block of $y$ ones, and all other cells blank. In the Lean model this is an equality of `FCP.BusyBeaver.run` results, which also implies that the machine has not halted at any earlier step.
-- source:
--   bbchallenge wiki, 5-state busy beaver winner, Analysis section, https://wiki.bbchallenge.org/wiki/1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA (Collatz-like rules attributed to Pascal Michel, Behavior of busy beavers, https://bbchallenge.org/~pascal.michel/beh#tm52a); also arXiv:2509.12337, Figure 1.

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg

namespace BB5

theorem g_3x1 (x : ℕ) :
    FCP.BusyBeaver.run winner (gcfg (3 * x + 1)) (5 * x^2 + 25 * x + 27) =
      some (gcfg (5 * x + 9)) := by sorry

end BB5
