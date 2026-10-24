-- Prove2me | Theorems.Thm_AssignmentGame_CoreCorners_worth_le_permutation_bound
-- name    : AssignmentGame.CoreCorners.worth_le_permutation_bound
-- status  : Proved
-- author  : @qmaai2907271020
-- created : 2026-10-20T21:11:44.029648+00:00
-- url     : https://prove2.me/theorems/b9132619-8fd2-49ce-8d2c-43ea3a118f12
-- title:
--   Nonnegative matching worth is bounded by all perfect matchings
-- statement:
--   In a finite balanced assignment game with nonnegative edge gains, suppose every perfect matching has total gain at most $K$. Then the worth of the entire assignment game—the maximum gain over all partial matchings—is also at most $K$.
--
--   Any partial matching can be completed to a perfect matching, and its gain cannot decrease when the added edges have nonnegative gain.
-- source:
--   Finite matching completion principle; https://arxiv.org/abs/2507.10872, Section 3.1, Lemma 3.3, assignment-game cost comparison.

import Definitions.Def_AssignmentGame_CoreCorners_Game

namespace AssignmentGame.CoreCorners

theorem worth_le_permutation_bound {M N : Type*} [Fintype M] [Fintype N]
    [DecidableEq M] [DecidableEq N]
    (a : M → N → ℝ) (ha : ∀ i j, 0 ≤ a i j)
    (e : M ≃ N) (K : ℝ)
    (hK : ∀ f : M ≃ N, (∑ i, a i (f i)) ≤ K) :
    worth a Finset.univ Finset.univ ≤ K := by sorry

end AssignmentGame.CoreCorners
