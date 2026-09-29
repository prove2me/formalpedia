-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_inv_shift_le
-- name    : BlockCycleRotation.sum_inv_shift_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T10:00:30.256796+00:00
-- url     : https://prove2.me/theorems/2dde3662-56d6-4a3d-8671-ac0334480501
-- title:
--   The reflection bound
-- statement:
--   **The reflection bound.** `∑_{j=1}^{a-1} 1/(a+j) ≤ 3/4`, from `1/(a+j) + 1/(2a-j) ≤ 3a/((a+1)(2a-1))`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `gTerm_row_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Numeric.lean#L70-L137

import Mathlib

open Real Finset Filter Topology

theorem BlockCycleRotation.sum_inv_shift_le (a : ℕ) :
    ∑ a' ∈ Finset.Ico 1 a, 1 / ((a : ℝ) + (a' : ℝ)) ≤ 3 / 4 := by sorry
