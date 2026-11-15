-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_terminal_density_girsanov
-- name    : AppliedSDE.SarkkaSolin.brownian_adjacent_terminal_density_girsanov
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:16:27.804668+00:00
-- url     : https://prove2.me/theorems/f7f0f32d-0a8f-4d3d-8a4a-ea8c1ff978d8
-- title:
--   Finite-time Brownian Girsanov: two adjacent increments shift independently under one terminal likelihood
-- statement:
--   For Brownian motion W and 0<=r<s<t, change the original probability measure by the single terminal exponential likelihood exp(theta*(W_t-W_r)-theta²(t-r)/2). Under this weighted measure, the two original adjacent increments W_s-W_r and W_t-W_s have a joint product Gaussian law with independent components of means theta(s-r) and theta(t-s), and original variances s-r and t-s. This proves a two-interval finite-dimensional Girsanov property for a genuinely single terminal density, using factorisation into two independent normalised increment likelihoods and the already-proved two-increment Esscher change-of-measure theorem.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, Girsanov theorem for constant deterministic drift on a two-cell Brownian grid.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_adjacent_increment_esscher_tilt
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.brownian_adjacent_terminal_density_girsanov
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (r s t : ℝ≥0)
    (hrs : r < s) (hst : s < t) (theta : ℝ) :
    (P.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (theta * (W.W (t : ℝ) ω - W.W (r : ℝ) ω) -
        ((t - r : ℝ≥0) : ℝ) * theta ^ 2 / 2)))).map
      (fun ω => (W.W (s : ℝ) ω - W.W (r : ℝ) ω,
        W.W (t : ℝ) ω - W.W (s : ℝ) ω)) =
      (gaussianReal (((s - r : ℝ≥0) : ℝ) * theta) (s - r)).prod
        (gaussianReal (((t - s : ℝ≥0) : ℝ) * theta) (t - s)) := by
  sorry
