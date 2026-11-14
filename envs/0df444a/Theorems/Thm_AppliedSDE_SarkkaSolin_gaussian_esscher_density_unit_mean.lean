-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_density_unit_mean
-- name    : AppliedSDE.SarkkaSolin.gaussian_esscher_density_unit_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:06:13.578108+00:00
-- url     : https://prove2.me/theorems/8fbc6f85-f007-4613-ad3f-c22719ebb00a
-- title:
--   Centred Gaussian exponential Esscher density has expectation one
-- statement:
--   If Z is Gaussian with mean zero and variance v>=0, the exponential likelihood ratio exp(theta Z-v theta^2/2) has expectation one for every real theta. This is a rigorous constant-drift change-of-measure normalisation ingredient for the open Girsanov Brownian-law core in Applied SDE Chapter 7. It follows from the published pinned Mathlib moment-generating function of a Gaussian and does not assert that the entire drift-corrected process is Brownian.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7, Gaussian likelihood and Girsanov change of measure.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussian_esscher_density_unit_mean
    (v : ℝ≥0) (theta : ℝ) :
    (∫ x : ℝ, Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2)
      ∂(gaussianReal 0 v)) = 1 := by
  sorry
