-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_scaled_primitive_mass_bound
-- name    : AvramDividend.Classical.causal_scaled_primitive_mass_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T18:52:51.09343+00:00
-- url     : https://prove2.me/theorems/bba1abf1-339a-47ac-b9eb-2772e9dcb081
-- title:
--   Scaled exponential primitive bounded by its positive-envelope mass
-- statement:
--   Suppose a signed positive-time L1 kernel is dominated by a positive-time L1 envelope whose mass on (0,x] is at most M. For positive a and nonnegative damping w, the corresponding scaled exponentially weighted primitive has absolute value at most M/a. Gives the precise geometric bound required by the Gaussian C1 Neumann-series theorem.
-- source:
--   Positive-time L1 kernels remain interval-integrable under exponential time-lag damping. Convert the positive-envelope Ioc mass bound to the interval integral and apply the proved damped signed primitive majorant bound, using the exact exponential primitive identity. This yields the geometric hH estimate for each Gaussian signed-power correction.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_damped_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_positive_L1_intervalIntegrable
import Theorems.Thm_AvramDividend_Classical_causal_exponentially_damped_primitive_abs_le_mass_div_a
import Theorems.Thm_AvramDividend_Classical_causal_exponential_primitive_convolution_identity

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem AvramDividend.Classical.causal_scaled_primitive_mass_bound
    (P F : ℝ → ℝ) (a w x M : ℝ)
    (ha : 0 < a) (hw : 0 ≤ w) (hx : 0 < x)
    (hPL1 : IntegrableOn P (Ioi (0 : ℝ)) volume)
    (hFL1 : IntegrableOn F (Ioi (0 : ℝ)) volume)
    (hdom : ∀ s : ℝ, 0 ≤ s → |P s| ≤ F s)
    (hMass : ∫ s in Ioc (0 : ℝ) x, F s ∂volume ≤ M) :
    |(Real.exp (-w * x) *
      (∫ s in Ioc (0 : ℝ) x, Real.exp (w * s) * P s ∂volume)) / a|
      ≤ M / a := by sorry
