-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_core_dual_constraints
-- name    : AssignmentGame.CoreCorners.core_dual_constraints
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:40:13.491997+00:00
-- url     : https://prove2.me/theorems/ce33a543-e902-4def-8485-d2d7572aa0f4
-- title:
--   Core payoffs satisfy assignment dual constraints
-- statement:
--   In a finite assignment game with edge gains $a_{ij}$, let $(u,v)$ belong to its core. Then every payoff coordinate is nonnegative and every possible pair satisfies
--
--   $$a_{ij}\leq u_i+v_j.$$
--
--   This extracts the nonnegative dual-feasibility conditions from the coalitional definition of the assignment-game core. It is reusable when translating core allocations into supporting courier wages.
-- source:
--   Shapley and Shubik (1971), The assignment game I: The core; https://arxiv.org/abs/2507.10872, Section 3.1, Lemma 3.3, assignment-game argument.

import Definitions.Def_AssignmentGame_CoreCorners_Game

namespace AssignmentGame.CoreCorners

theorem core_dual_constraints {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (u : M → ℝ) (v : N → ℝ)
    (hcore : (u, v) ∈ core a) :
    (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
      ∀ i j, a i j ≤ u i + v j := by sorry

end AssignmentGame.CoreCorners
