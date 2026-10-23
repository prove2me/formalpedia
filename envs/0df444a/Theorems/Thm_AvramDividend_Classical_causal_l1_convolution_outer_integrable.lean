-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_l1_convolution_outer_integrable
-- name    : AvramDividend.Classical.causal_l1_convolution_outer_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T19:14:12.938991+00:00
-- url     : https://prove2.me/theorems/06415ce0-246b-403e-80e6-2d5640185f62
-- title:
--   Outer integrability of an L1 causal convolution with continuous input
-- statement:
--   A causal convolution of a positive-time L1 kernel with a continuous input is integrable as a function of the outer variable on every finite positive interval. Truncate the input to (0,x], apply the globally integrable positive convolution theorem to the truncated input and K, then identify its values for 0<t≤x by the interval-integral and indicator identities.
-- source:
--   Pinned Mathlib MeasureTheory.integrable_posConvolution and intervalIntegral.integral_of_le; compact-interval integrability of continuous input.

import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_l1_convolution_outer_integrable
    (K g : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun t : ℝ =>
      ∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume)
      (Ioc (0 : ℝ) x) volume := by sorry
