-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_inv_min_le
-- name    : BlockCycleRotation.sum_inv_min_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:52:15.088377+00:00
-- url     : https://prove2.me/theorems/a3bbca3e-53d7-493a-bc86-7f2174656d5d
-- title:
--   The `log a` factor
-- statement:
--   **The `log a` factor.** `∑_{0<m<a} 1/min(m, a-m) ≤ 2 ∑_{0<m<a} 1/m`.
--
--   In Blomer–Bux this is **Lemma 16**, “`log a` factor, `∑ 1/min(m,a−m)`”. It is used in the proof of `norm_sum_twisted_le`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- Lemma 16. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L144-L159

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_inv_min_le (a : ℕ) :
    ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ)
      ≤ 2 * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by sorry
