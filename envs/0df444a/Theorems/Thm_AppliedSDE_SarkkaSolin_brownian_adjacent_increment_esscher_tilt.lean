-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_increment_esscher_tilt
-- name    : AppliedSDE.SarkkaSolin.brownian_adjacent_increment_esscher_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:07:32.807036+00:00
-- url     : https://prove2.me/theorems/65ae5338-b0cd-4d09-b250-e4272ac18e9c
-- title:
--   Two adjacent Brownian increments remain independent shifted Gaussians under constant-drift exponential measure tilt
-- statement:
--   For Brownian motion W on any probability space and strictly increasing nonnegative times r<s<t, weight the original measure by the product of exponential likelihood ratios for the increments W_s-W_r and W_t-W_s with the same deterministic drift theta. The joint law of those two increments under the weighted measure equals the product of independent Gaussian distributions with means theta(s-r) and theta(t-s), preserving their original variances. This is a concrete two-interval finite-dimensional Girsanov theorem for the original Brownian path, not merely an abstract Gaussian product identity.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, finite-dimensional Girsanov shift of Brownian increments.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_increments_product_gaussian
import Theorems.Thm_AppliedSDE_SarkkaSolin_joint_gaussian_increment_esscher_under_weighted_measure
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.brownian_adjacent_increment_esscher_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (r s t : ℝ≥0)
    (hrs : r < s) (hst : s < t) (theta : ℝ) :
    let X : Ω → ℝ := fun ω => W.W (s : ℝ) ω - W.W (r : ℝ) ω
    let Y : Ω → ℝ := fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω
    (P.withDensity (fun ω =>
      ENNReal.ofReal
        (Real.exp (theta * X ω - ((s - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)) *
      ENNReal.ofReal
        (Real.exp (theta * Y ω - ((t - s : ℝ≥0) : ℝ) * theta ^ 2 / 2)))).map
        (fun ω => (X ω, Y ω)) =
      (gaussianReal (((s - r : ℝ≥0) : ℝ) * theta) (s - r)).prod
        (gaussianReal (((t - s : ℝ≥0) : ℝ) * theta) (t - s)) := by
  sorry
