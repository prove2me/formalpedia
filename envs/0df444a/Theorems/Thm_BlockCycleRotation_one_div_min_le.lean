-- Prove2me | Theorems.Thm_BlockCycleRotation_one_div_min_le
-- name    : BlockCycleRotation.one_div_min_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:10.951598+00:00
-- url     : https://prove2.me/theorems/82e11290-f5ed-4076-ae31-521d83e76980
-- title:
--   `1/min(m, a-m) ≤ 1/m + 1/(a-m)`
-- statement:
--   `1/min(m, a-m) ≤ 1/m + 1/(a-m)`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `sum_inv_min_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L129-L142

import Mathlib

open Real Finset

theorem BlockCycleRotation.one_div_min_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ) ≤ 1 / (m : ℝ) + 1 / ((a - m : ℕ) : ℝ) := by sorry
