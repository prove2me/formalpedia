-- Prove2me | Theorems.Thm_BlockCycleRotation_double_sum_eq_pairs
-- name    : BlockCycleRotation.double_sum_eq_pairs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:58:12.363577+00:00
-- url     : https://prove2.me/theorems/7d1f683b-696d-44b9-bfaf-1ff0a2c38220
-- title:
--   The double sum as a sum over pairs
-- statement:
--   The double sum as a sum over pairs.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `bulk_double_le_pairs`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L345-L363

import Mathlib

open Real Finset

theorem BlockCycleRotation.double_sum_eq_pairs {N : ℕ} (f : ℕ → ℕ → ℝ) :
    ∑ a ∈ Finset.range (N + 1), ∑ a' ∈ Finset.range a, f a a'
      = ∑ p ∈ ((Finset.range (N + 1)) ×ˢ (Finset.range (N + 1))).filter (fun p => p.2 < p.1),
          f p.1 p.2 := by sorry
