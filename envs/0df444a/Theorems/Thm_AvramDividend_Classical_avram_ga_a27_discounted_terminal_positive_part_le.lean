-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a27_discounted_terminal_positive_part_le
-- name    : AvramDividend.Classical.avram_ga_a27_discounted_terminal_positive_part_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:23:08.151567+00:00
-- url     : https://prove2.me/theorems/6aa2d670-1b8e-4702-bc18-30cab5501591
-- title:
--   Discounted terminal Gaussian positive increment bounded using one-sided values
-- statement:
--   For nonnegative discount q and nonnegative time t, the positive part of the discounted difference of two real values is bounded by the positive part of the first value and the negative part of the second. Supports a one-sided envelope for the final clipped Gaussian cell.
-- source:
--   Avram gledger179 positive-clock terminal clipped Gaussian cell bounds

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a27_discounted_terminal_positive_part_le
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0) (a b : ℝ) :
    max (Real.exp (-(q * (t : ℝ))) * (a - b)) 0 ≤
      max a 0 + max (-b) 0 := by sorry
