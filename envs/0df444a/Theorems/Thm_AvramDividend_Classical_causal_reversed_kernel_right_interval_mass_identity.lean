-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_reversed_kernel_right_interval_mass_identity
-- name    : AvramDividend.Classical.causal_reversed_kernel_right_interval_mass_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:20:36.588048+00:00
-- url     : https://prove2.me/theorems/1da8687e-079c-4032-8961-e99c7a54341f
-- title:
--   Reversed causal kernel integral on right interval equals truncated kernel mass
-- statement:
--   Reflect the interval u≤s≤x through t=x-s. The reversed kernel integral ∫_u^x κ(x-s)ds becomes ∫_0^(x-u) κ(t)dt, with the interval integral orientation handled by the pinned Mathlib change-of-variables theorem. This is the right-mass identity for the convolution-power split.
-- source:
--   Pinned Mathlib intervalIntegral.integral_comp_sub_left at revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open MeasureTheory Set

theorem AvramDividend.Classical.causal_reversed_kernel_right_interval_mass_identity
    (κ : ℝ → ℝ) (x u : ℝ) :
    (∫ s in u..x, κ (x - s)) =
      ∫ t in (0 : ℝ)..(x - u), κ t := by sorry
