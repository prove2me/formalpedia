-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_inv_le_one_add_log
-- name    : BlockCycleRotation.sum_inv_le_one_add_log
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:09.430735+00:00
-- url     : https://prove2.me/theorems/37bf1d56-a0a5-4223-bf0a-55c4380df1a6
-- title:
--   `∑_{0<m<a} 1/m ≤ 1 + log a`
-- statement:
--   `∑_{0<m<a} 1/m ≤ 1 + log a`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Progression.lean#L110-L130

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_inv_le_one_add_log (a : ℕ) :
    ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) ≤ 1 + Real.log a := by sorry
