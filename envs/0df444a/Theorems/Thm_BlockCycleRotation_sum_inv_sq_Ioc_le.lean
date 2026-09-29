-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_inv_sq_Ioc_le
-- name    : BlockCycleRotation.sum_inv_sq_Ioc_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:57:39.761623+00:00
-- url     : https://prove2.me/theorems/549a54db-f1ee-46ac-87c4-6d77379b2398
-- title:
--   Telescoping: `∑_{N < a ≤ M} 1/a² ≤ 1/N - 1/M`
-- statement:
--   Telescoping: `∑_{N < a ≤ M} 1/a² ≤ 1/N - 1/M`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `sum_inv_sq_tail_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Constant.lean#L163-L181

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_inv_sq_Ioc_le {N : ℕ} (hN : 0 < N) :
    ∀ M, N ≤ M → ∑ a ∈ Finset.Ioc N M, 1 / ((a : ℝ) ^ 2) ≤ 1 / (N : ℝ) - 1 / (M : ℝ) := by sorry
