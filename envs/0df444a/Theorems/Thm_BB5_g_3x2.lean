-- Prove2me | Theorems.Thm_BB5_g_3x2
-- name    : BB5.g_3x2
-- status  : Proved
-- author  : @loader3229
-- created : 2026-11-22T14:39:37.081603+00:00
-- url     : https://prove2.me/theorems/1ca0ae12-a4c5-4ffe-88b6-a98fa5e696b7
-- title:
--   Collatz rule $g(3x+2)\to^{6x+12}$ halt
-- statement:
--   For every $x\in\mathbb{N}$, the five-state champion started in configuration $g(3x+2)$ halts after exactly $6x+12$ transitions, and not earlier:
--
--   $$g(3x+2)\longrightarrow^{\,6x+12\,}0^\infty 1^{\mathbb{Z}}\triangleright 0\,1^{x+1}0^\infty .$$
--
--   Here $g(y)$ is the configuration with the machine in state $A$, its head on the blank cell immediately to the left of a block of $y$ ones. In the Lean model `HaltsIn winner (gcfg (3*x+2)) (6*x+12)` asserts that the run returns `none` at step $6x+12$ and is not `none` at any earlier step.
-- source:
--   bbchallenge wiki, 5-state busy beaver winner, Analysis section, https://wiki.bbchallenge.org/wiki/1RB1LC_1RC1RB_1RD0LE_1LA1LD_1RZ0LA (Collatz-like rules attributed to Pascal Michel, Behavior of busy beavers, https://bbchallenge.org/~pascal.michel/beh#tm52a); also arXiv:2509.12337, Figure 1.

import Mathlib
import Definitions.Def_FCP_BusyBeaver
import Definitions.Def_BB5_winner
import Definitions.Def_BB5_gcfg

namespace BB5

theorem g_3x2 (x : ℕ) :
    FCP.BusyBeaver.HaltsIn winner (gcfg (3 * x + 2)) (6 * x + 12) := by sorry

end BB5
