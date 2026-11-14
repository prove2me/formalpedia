-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_density_shift
-- name    : AppliedSDE.SarkkaSolin.gaussian_esscher_density_shift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:09:04.875548+00:00
-- url     : https://prove2.me/theorems/6d3c1c96-5d4d-42ba-9acb-fe40f5b85ac0
-- title:
--   Gaussian exponential tilt shifts the mean by variance times drift
-- statement:
--   For a centred real Gaussian density with strictly positive variance v and real tilt theta, multiplying the density by exp(theta*x-v theta^2/2) yields exactly the Gaussian density with the same variance v and mean v*theta. This pointwise completion-of-the-square identity is the finite-increment change-of-law component of Girsanov's theorem and supports Applied SDE Chapter 7. It is a genuine equality of densities, with Brownian process-level consistency still a separate obligation.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7, Gaussian likelihood and Girsanov change of measure.

import Mathlib
open ProbabilityTheory
open scoped NNReal

theorem AppliedSDE.SarkkaSolin.gaussian_esscher_density_shift
    (v : ℝ≥0) (hv : 0 < v) (theta x : ℝ) :
    gaussianPDFReal ((v : ℝ) * theta) v x =
      gaussianPDFReal 0 v x *
        Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2) := by
  sorry
