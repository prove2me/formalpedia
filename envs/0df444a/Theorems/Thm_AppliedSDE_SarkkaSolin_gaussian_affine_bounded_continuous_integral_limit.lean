-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_affine_bounded_continuous_integral_limit
-- name    : AppliedSDE.SarkkaSolin.gaussian_affine_bounded_continuous_integral_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:07:21.06421+00:00
-- url     : https://prove2.me/theorems/29ad2061-2524-441f-a11e-43366f991598
-- title:
--   Dominated convergence for vanishing affine Gaussian perturbations of bounded continuous functions
-- statement:
--   For any bounded continuous test function and positive q, the standard-normal expectation of f(sqrt(q*h)*Z+y+b*h) converges to f(y) as h tends to zero from the right. This is the continuous-mapping plus dominated-convergence statement behind the narrow Gaussian Dirac limit.
-- source:
--   Sarkka and Solin (2019), Chapter 5 Gaussian transition-density initial condition. Mathlib MeasureTheory.tendsto_integral_filter_of_norm_le_const.

import Mathlib
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussian_affine_bounded_continuous_integral_limit
    (b q y : ℝ) (hq : 0 < q)
    (f : ℝ -> ℝ) (hf : Continuous f)
    (hfb : ∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) :
    Tendsto
      (fun h : ℝ => ∫ z : ℝ,
        f (Real.sqrt (q * h) * z + (y + b * h))
          ∂(gaussianReal 0 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
  sorry
