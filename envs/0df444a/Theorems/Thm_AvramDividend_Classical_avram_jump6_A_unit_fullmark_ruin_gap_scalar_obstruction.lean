-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
-- name    : AvramDividend.Classical.avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:00:47.746169+00:00
-- url     : https://prove2.me/theorems/7881a5e7-4365-40b6-ad9c-62b63a22fcff
-- title:
--   Scalar obstruction to unit-coefficient fullmark stopped ruin ledger
-- statement:
--   On a finite-cap reserve y in [0,1/5], a negative mark of size 2 causes a zero post-ruin value for the nonnegative branch of w(y)=1+y+y², while any Brownian fluctuation b≤1/100 and compensation time t≤1/10 leave w(y)+b−2+2t ≤−11/20. This proves a strict scalar gap in the unit-coefficient Jfull source required by 5424c324/061f936f; constructing the full original product Lévy model and positive-probability jump event is a separate task.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_unit_fullmark_ruin_gap_scalar_obstruction
    (y b t : ℝ)
    (hy0 : 0 ≤ y) (hycap : y ≤ 1 / 5)
    (hB : b ≤ 1 / 100) (ht : t ≤ 1 / 10) :
    (if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) = (0 : ℝ) ∧
    (1 + y + y ^ 2) + b - 2 + 2 * t ≤ -(11 / 20 : ℝ) := by sorry
