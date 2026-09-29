-- Prove2me | Theorems.Thm_BlockCycleRotation_two_mul_min_div_le_sin
-- name    : BlockCycleRotation.two_mul_min_div_le_sin
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:51:57.837455+00:00
-- url     : https://prove2.me/theorems/7dc36e46-2562-4a11-a32e-ee849fd97d93
-- title:
--   Jordan's inequality at a root of unity
-- statement:
--   **Jordan's inequality at a root of unity.** For `0 < m < a`, `2 · min(m, a-m) / a ≤ sin (π m / a)`. The two cases are `m ≤ a/2`, where Jordan applies directly, and `m > a/2`, where it applies after reflecting via `sin (π - x) = sin x`.
--
--   This is an auxiliary lemma of the formalization rather than a result stated in the paper. It is used in the proof of `four_mul_min_div_le_norm`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Characters.lean#L25-L66

import Mathlib

open Real Finset

theorem BlockCycleRotation.two_mul_min_div_le_sin {a m : ℕ} (h0 : 0 < m) (hma : m < a) :
    2 * ((min m (a - m) : ℕ) : ℝ) / (a : ℝ) ≤ Real.sin (π * m / a) := by sorry
