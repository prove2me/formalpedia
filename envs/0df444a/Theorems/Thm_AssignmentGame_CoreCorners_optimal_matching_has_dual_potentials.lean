-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_optimal_matching_has_dual_potentials
-- name    : AssignmentGame.CoreCorners.optimal_matching_has_dual_potentials
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T20:40:50.360489+00:00
-- url     : https://prove2.me/theorems/3dc913f4-2d4a-4efb-b7c4-245dd3cd1e79
-- title:
--   Optimal matching admits tight nonnegative dual potentials
-- statement:
--   For a finite assignment game with nonnegative edge gains, let $P$ be a maximum-weight matching. There exist nonnegative payoffs $u_i,v_j$ such that
--
--   $$a_{ij}\leq u_i+v_j$$
--
--   on every edge and equality holds for every edge of $P$. This is the complementary-slackness certificate used to turn a cost-minimizing courier assignment into supporting wages.
-- source:
--   Shapley and Shubik (1971), The assignment game I: The core; https://arxiv.org/abs/2507.10872, Section 3.1, Lemma 3.3.

import Definitions.Def_AssignmentGame_CoreCorners_Game

namespace AssignmentGame.CoreCorners

theorem optimal_matching_has_dual_potentials {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (P : Finset (M × N)) (hP : IsMatching Finset.univ Finset.univ P)
    (hopt : ∑ p ∈ P, a p.1 p.2 = worth a Finset.univ Finset.univ) :
    ∃ (u : M → ℝ) (v : N → ℝ),
      (∀ i, 0 ≤ u i) ∧ (∀ j, 0 ≤ v j) ∧
      (∀ i j, a i j ≤ u i + v j) ∧
      (∀ p ∈ P, u p.1 + v p.2 = a p.1 p.2) := by sorry

end AssignmentGame.CoreCorners
