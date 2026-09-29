-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_inv_sq_shift_ge
-- name    : BlockCycleRotation.sum_inv_sq_shift_ge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:50.688675+00:00
-- url     : https://prove2.me/theorems/870a363f-ca4f-413a-a4c9-7f6f2bedd089
-- title:
--   sum inv sq shift ge
-- statement:
--   A supporting lemma of the formalization, declared as `sum_inv_sq_shift_ge`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `gTerm_row_ge`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L338-L383

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.sum_inv_sq_shift_ge {a : ℕ} (ha : 1 ≤ a) :
    4 * ((a : ℝ) - 1) / (9 * (a : ℝ) ^ 2)
      ≤ ∑ j ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (j : ℝ)) ^ 2 := by sorry
