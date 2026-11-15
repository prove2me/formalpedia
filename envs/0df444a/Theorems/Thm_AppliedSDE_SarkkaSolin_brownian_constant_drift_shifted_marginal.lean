-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_constant_drift_shifted_marginal
-- name    : AppliedSDE.SarkkaSolin.brownian_constant_drift_shifted_marginal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:44:57.530196+00:00
-- url     : https://prove2.me/theorems/e2c0b67b-f954-43d2-9f2b-f1c929b6683f
-- title:
--   Brownian marginal law under deterministic exponential Girsanov change of measure
-- statement:
--   Let W be Brownian motion under P, let t>0, and let theta be constant. Weight P by the exponential terminal likelihood exp(theta W_t - t theta²/2) and push this weighted measure forward by W_t. The resulting law is precisely the Gaussian distribution with mean t theta and variance t. This is the finite-time marginal change-of-measure assertion of Girsanov for deterministic drift, derived from Brownian marginal Gaussianity, the Gaussian Esscher measure identity, and a general pushforward-density transport lemma.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7 (Girsanov under constant drift).

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
import Theorems.Thm_LevyStochCalc_Brownian_BrownianMotion_hasLaw_eval_readable
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_tilt_measure
import Theorems.Thm_AppliedSDE_SarkkaSolin_likelihood_tilt_pushforward
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.brownian_constant_drift_shifted_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (t : ℝ≥0) (ht : 0 < t) (theta : ℝ) :
    (P.withDensity
        (fun ω => ENNReal.ofReal
          (Real.exp (theta * W.W (t : ℝ) ω -
            (t : ℝ) * theta ^ 2 / 2)))).map
        (W.W (t : ℝ)) =
      gaussianReal ((t : ℝ) * theta) t := by
  sorry
