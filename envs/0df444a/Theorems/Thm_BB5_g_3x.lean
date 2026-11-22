-- Prove2me | Theorems.Thm_BB5_g_3x
-- name    : BB5.g_3x
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-22T14:39:36.035701+00:00
-- url     : https://prove2.me/theorems/b5e9c616-38b3-4d4a-94de-86d227158240
-- title:
--   Collatz rule $g(3x)\to^{5x^2+19x+15}g(5x+6)$
-- statement:
--   For every $x\in\mathbb{N}$, the five-state champion started in configuration $g(3x)$ reaches $g(5x+6)$ after exactly $5x^2+19x+15$ transitions:
--
--   $$g(3x)\longrightarrow^{\,5x^2+19x+15\,}g(5x+6).$$
--
--   Here $g(y)$ is the configuration with the machine in state $A$, its head on the blank cell immediately to the left of a block of $y$ ones, and all other cells blank. In the Lean model this is an equality of `FCP.BusyBeaver.run` results, which also implies that the machine has not halted at any earlier step.
-- source:
--   bbchallenge wiki, 5-state busy beaver winner, Analysis section, https://wiki.bbchallenge.org/wiki/1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA (Collatz-like rules attributed to Pascal Michel, Behavior of busy beavers, https://bbchallenge.org/~pascal.michel/beh#tm52a); also arXiv:2509.12337, Figure 1.

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg

namespace BB5

theorem g_3x (x : ℕ) :
    FCP.BusyBeaver.run winner (gcfg (3 * x)) (5 * x^2 + 19 * x + 15) =
      some (gcfg (5 * x + 6)) := by sorry

end BB5
