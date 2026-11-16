-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a554_discounted_difference_positive_exp_upper
-- name    : AvramDividend.Classical.avram_ga_a554_discounted_difference_positive_exp_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:04:43.597463+00:00
-- url     : https://prove2.me/theorems/3036dd7d-564d-43c9-a735-dbf7cd1ee495
-- title:
--   One-sided positive bound for a discounted endpoint value difference
-- statement:
--   With a nonnegative discount bounded by one, an upper exponential bound on the endpoint value and absolute bounded initial value imply a positive-part estimate of their discounted difference, without controlling the endpoint negative tail.
-- source:
--   Positive discount and the inequality max(e(a-b),0)≤max(a-b,0), plus one-sided upper bounds

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_ga_a554_discounted_difference_positive_exp_upper
    (a b e θ K M z : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ha : a ≤ K * Real.exp (θ * z))
    (hb : |b| ≤ M) :
    max (e * (a - b)) (0 : ℝ) ≤
      K * Real.exp (θ * z) + M := by sorry
