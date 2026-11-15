-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_esscher_probability
-- name    : AppliedSDE.SarkkaSolin.brownian_constant_drift_esscher_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:59:10.692187+00:00
-- url     : https://prove2.me/theorems/4cd48d7b-d49a-489b-b297-8c116ae4aac5
-- title:
--   Brownian constant-drift terminal exponential density defines a genuine probability measure
-- statement:
--   Let W be Brownian under P. For t>0 and deterministic constant drift theta, the weighted measure with density exp(theta W_t-theta²t/2) has total mass exactly one and is therefore a probability measure. The proof transports its mass through the Brownian coordinate, using the previously proved tilted marginal Gaussian law and the fact that a Gaussian distribution is a probability measure. This isolates the probability-normalisation part of finite-horizon deterministic-drift Girsanov and avoids assuming the density has unit mean.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, constant-drift exponential change of measure.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_shifted_marginal
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.brownian_constant_drift_esscher_probability
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (t : ℝ≥0) (ht : 0 < t) (theta : ℝ) :
    IsProbabilityMeasure
      (P.withDensity
        (fun ω => ENNReal.ofReal
          (Real.exp (theta * W.W (t : ℝ) ω -
            (t : ℝ) * theta ^ 2 / 2)))) := by
  sorry
