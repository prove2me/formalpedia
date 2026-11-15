-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_brownian_increment_gaussian_law
-- name    : AppliedSDE.SarkkaSolin.brownian_increment_gaussian_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:46:52.920577+00:00
-- url     : https://prove2.me/theorems/252d4cf3-26ae-4c61-b5be-b4430423d35a
-- title:
--   Gaussian law of Brownian increments over any nonnegative interval
-- statement:
--   For a Brownian motion W on a probability space and nonnegative times s<=t, the increment W_t-W_s has Gaussian law of mean zero and variance t-s. The zero-length interval is handled by a deterministic zero law; the positive interval uses the native Brownian increment Gaussian distribution field. This prepares finite-dimensional deterministic-drift Girsanov proofs.
-- source:
--   LevyStochCalc Brownian/MathlibBridge.lean (Apache-2.0), Brownian marginal bridge; Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_MathlibBridge
open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian
open scoped NNReal

theorem AppliedSDE.SarkkaSolin.brownian_increment_gaussian_law
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t) :
    HasLaw
      (fun ω => W.W (t : ℝ) ω - W.W (s : ℝ) ω)
      (gaussianReal 0 (t - s)) P := by
  sorry
