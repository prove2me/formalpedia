-- Prove2me | Theorems.Thm_AssignmentGame_CoreLP_dualObj_eq_worth_of_dual_optimal
-- name    : AssignmentGame.CoreLP.dualObj_eq_worth_of_dual_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:16:27.725278+00:00
-- url     : https://prove2.me/theorems/baf3d538-d61e-4e8b-95df-fd3efdc579c6
-- title:
--   Eq. (3.5) — every optimal dual solution distributes exactly $v(M \cup N)$
-- statement:
--   Let $M$ and $N$ be finite sets and $a = (a_{ij})$ a matrix with $a_{ij} \ge 0$. If $(u, v)$ minimises $w = \sum_i u_i + \sum_j v_j$ subject to $u_i \ge 0$, $v_j \ge 0$ and $u_i + v_j \ge a_{ij}$ for all $i, j$ (the dual assignment LP (3.3)–(3.4)), then
--   $$\sum_{i \in M} u_i + \sum_{j \in N} v_j = v(M \cup N),$$
--   the worth (2.6) of the coalition of all players.
--
--   Since the dual variables are nonnegative, this says that an optimal dual solution is an imputation of the assignment game.
-- source:
--   Shapley and Shubik, The Assignment Game I: The Core, Int. J. Game Theory 1 (1971), p. 118, Eq. (3.5)

import Mathlib
import Definitions.Def_AssignmentGame_CoreLP_Game

open Finset

namespace AssignmentGame.CoreLP

theorem dualObj_eq_worth_of_dual_optimal {M N : Type*} [Fintype M] [Fintype N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j) (p : (M → ℝ) × (N → ℝ))
    (hp : DualOptimal a p) :
    ∑ i, p.1 i + ∑ j, p.2 j = worth a univ univ := by sorry

end AssignmentGame.CoreLP
