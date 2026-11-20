-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_caplinear_finitecap_payoff_cell_secant
-- name    : AvramDividend.Classical.avram_a19_caplinear_finitecap_payoff_cell_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:45:32.115735+00:00
-- url     : https://prove2.me/theorems/9200ad77-748e-47db-80ae-393079e6cc68
-- title:
--   Cap-linear dividend payment cell secant inequality
-- statement:
--   At the original finite dividend cap, suppose y is a postpayment reserve at or below the cap and d is a nonnegative dividend increment. An interior one-sided secant gradient lower bound w(z)-w(y)>=z-y for y<=z<=C ensures that cap-linear continuation V satisfies V(y+d)-w(y)>=d even when the intermediate prepayment reserve y+d exceeds C. This explicitly removes the raw w(Z) above-cap gap in finite stopped dividend cells; deriving the secant from HJB deriv w>=1 and constructing full stochastic Ito remains separate.
-- source:
--   Original stopped HJB finite-cap right-dividend grid cell: scalar slope continuation across cap, valid for cap crossings without evaluating unregulated w above C.

import Mathlib

/-- Cap-linear continuation preserves the interior one-sided dividend slope for a prepayment overshoot. -/
theorem AvramDividend.Classical.avram_a19_caplinear_finitecap_payoff_cell_secant
    (w : ℝ → ℝ) (C y d : ℝ) (hy : y ≤ C) (hd : 0 ≤ d)
    (hSlope : ∀ z : ℝ, y ≤ z → z ≤ C →
      z - y ≤ w z - w y) :
    let V : ℝ → ℝ := fun z => if z ≤ C then w z else w C + (z - C)
    d ≤ V (y + d) - w y := by sorry
