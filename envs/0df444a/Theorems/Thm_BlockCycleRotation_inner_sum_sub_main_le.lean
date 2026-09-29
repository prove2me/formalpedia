-- Prove2me | Theorems.Thm_BlockCycleRotation_inner_sum_sub_main_le
-- name    : BlockCycleRotation.inner_sum_sub_main_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-05T09:55:17.054287+00:00
-- url     : https://prove2.me/theorems/c9c1634c-9210-4170-be1c-d02d439521cf
-- title:
--   The inner sum of the triple sum
-- statement:
--   **The inner sum of the triple sum.** For fixed `d`, `a`, `a'`, summing the paper's linear function over an arithmetic progression modulo `a` differs from its expected value by `O(log a)`. This is `sum_ap_sub_main_le_log` at the paper's coefficients.
--
--   In Blomer–Bux this is **§4**, “Triple sum: inner sum over `b'`”.
-- source:
--   Valentin Blomer and Kai-Uwe Bux, "The cost of cyclic permutations and remainder sums in the Euclidean algorithm", AofA 2026, LIPIcs vol. 381, pp. 14:1-14:17, doi:10.4230/LIPIcs.AofA.2026.14. Numbering follows the full version, arXiv:2601.00979v1 -- §4. Lean source: https://github.com/dbenbenn/block-cycle-rotation/blob/f69003fd8b00c9b5d6d1a4f6807b4943bce0a92c/BlockCycleRotation/TripleSum.lean#L35-L47

import Mathlib

open Real Finset

theorem BlockCycleRotation.inner_sum_sub_main_le (n d a a' : ℕ) (ha : 0 < a) (c : ℤ) (U : ℕ) :
    ‖(∑ b ∈ Finset.Ico 1 U, if (a : ℤ) ∣ ((b : ℤ) - c) then
          (((n : ℂ) / (d * a) + d * a) + (-(a' : ℂ) / a) * b) else 0)
        - (1 / (a : ℂ)) * ∑ b ∈ Finset.Ico 1 U,
            (((n : ℂ) / (d * a) + d * a) + (-(a' : ℂ) / a) * b)‖
      ≤ (‖((n : ℂ) / (d * a) + d * a)‖ + ‖(-(a' : ℂ) / a)‖ * (U - 1 : ℕ))
          * (1 + Real.log a) := by sorry
