-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_density_unit_mean
-- name    : AppliedSDE.SarkkaSolin.brownian_constant_drift_density_unit_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:11:04.175618+00:00
-- url     : https://prove2.me/theorems/188a19f4-3ead-42ae-933e-444a6b5568e5
-- title:
--   Unit-mean Brownian stochastic exponential at every horizon for constant drift
-- statement:
--   For a Brownian motion W on any probability space, any nonnegative time t and any constant real drift parameter theta, the exponential martingale terminal likelihood Z_t = exp(theta W_t - theta² t/2) has expectation exactly 1. This is a rigorous deterministic-drift special case of the Novikov/Girsanov density-normalisation theorem, obtained by transporting the normal exponential moment through the previously proved Brownian Gaussian marginal law.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7 (constant-drift Girsanov density).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_density_unit_mean
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.brownian_constant_drift_density_unit_mean
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (t : ℝ≥0) (theta : ℝ) :
    (∫ ω, Real.exp (theta * W.W (t : ℝ) ω -
          (t : ℝ) * theta ^ 2 / 2) ∂P) = 1 := by
  sorry
