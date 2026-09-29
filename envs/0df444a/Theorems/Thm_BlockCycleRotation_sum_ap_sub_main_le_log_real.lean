-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_ap_sub_main_le_log_real
-- name    : BlockCycleRotation.sum_ap_sub_main_le_log_real
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:56:31.584369+00:00
-- url     : https://prove2.me/theorems/f6b750e7-8c07-449b-9bce-f9d1ba86cec0
-- title:
--   The progression estimate, over `ℝ`
-- statement:
--   The progression estimate, over `ℝ`.
--
--   In Blomer–Bux this is **§4**, “Progression estimate over `ℝ`”. It is used in the proof of `inner_gt_estimate`.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L865-L880

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_ap_sub_main_le_log_real {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℝ) (T : ℕ) :
    |(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℝ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)|
      ≤ (|A| + |B| * (T - 1 : ℕ)) * (1 + Real.log a) := by sorry
