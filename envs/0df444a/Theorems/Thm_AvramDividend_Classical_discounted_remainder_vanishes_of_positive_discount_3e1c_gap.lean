-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_remainder_vanishes_of_positive_discount_3e1c_gap
-- name    : AvramDividend.Classical.discounted_remainder_vanishes_of_positive_discount_3e1c_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T10:52:14.638731+00:00
-- url     : https://prove2.me/theorems/5259c454-d077-4716-8b7b-a19bb4b77806
-- title:
--   Discounted remainder vanishes for positive discount
-- statement:
--   For a strictly positive discount rate q and any constant C, the discounted remainder exp(-q t) * C tends to 0 as t tends to infinity. This is the deterministic vanishing-remainder step in the two-sided exit identity before ruin: the stopped killed-scale martingale leaves a no-exit remainder bounded by exp(-q t) * W a, which vanishes in the passage limit and isolates the exact W x / W a exit value.
-- source:
--   Deterministic real-analysis step supporting AvramDividend.Classical.two_sided_exit_before_ruin_integral_identity (3e1ce2c8-c846-4e0f-8e4f-4fcbd9a0d4d7): the vanishing discounted no-exit remainder in the upper/lower exit passage (see candidates/work_on/3e1ce2c8_active_20261029.md). Pure Mathlib filter/tendsto calculus; no process data.

import Mathlib
open Filter Topology

theorem AvramDividend.Classical.discounted_remainder_vanishes_of_positive_discount_3e1c_gap
    (q C : ℝ) (hq : 0 < q) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(q * t)) * C) Filter.atTop (nhds 0) := by sorry
