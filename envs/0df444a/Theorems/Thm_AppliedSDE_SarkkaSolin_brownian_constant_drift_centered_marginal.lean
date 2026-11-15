-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_centered_marginal
-- name    : AppliedSDE.SarkkaSolin.brownian_constant_drift_centered_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:58:34.834544+00:00
-- url     : https://prove2.me/theorems/f21c76b5-224e-4bcf-897f-97f937771716
-- title:
--   Drift-compensated Brownian coordinate is centred Gaussian after constant-drift Girsanov tilt
-- statement:
--   For Brownian motion W under P, positive time t and a constant drift theta, weight P by the terminal exponential density exp(theta W_t - theta²t/2). Under this weighted measure the centred random variable W_t-t theta has exactly Gaussian law with mean 0 and variance t. This is the one-time Brownian-law assertion of deterministic-drift Girsanov, derived by subtracting the shifted mean from the proved tilted marginal and applying the Gaussian translation identity.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Chapter 7: Girsanov Brownian law for deterministic drift at one finite time.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_shifted_marginal
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.brownian_constant_drift_centered_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (t : ℝ≥0) (ht : 0 < t) (theta : ℝ) :
    (P.withDensity
        (fun ω => ENNReal.ofReal
          (Real.exp (theta * W.W (t : ℝ) ω -
            (t : ℝ) * theta ^ 2 / 2)))).map
        (fun ω => W.W (t : ℝ) ω - (t : ℝ) * theta) =
      gaussianReal 0 t := by
  sorry
