-- Prove2me | Theorems.Thm_BlockCycleRotation_sum_ap_sub_main_le
-- name    : BlockCycleRotation.sum_ap_sub_main_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:53:06.728307+00:00
-- url     : https://prove2.me/theorems/cd5f9d5f-1084-4380-b16a-73e5417a7627
-- title:
--   Sums over an arithmetic progression
-- statement:
--   **Sums over an arithmetic progression.** Replacing the sum by its expected value costs a harmonic sum, i.e. `O(log a)`.
--
--   In Blomer–Bux this is **§4**, “Sum over an AP”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/Progression.lean#L77-L102

import Mathlib

open Real Finset

theorem BlockCycleRotation.sum_ap_sub_main_le {a : ℕ} (ha : 0 < a) (c : ℤ) (A B : ℂ) (T : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 T, if (a : ℤ) ∣ ((b : ℤ) - c) then (A + B * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 T, (A + B * b)‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by sorry
