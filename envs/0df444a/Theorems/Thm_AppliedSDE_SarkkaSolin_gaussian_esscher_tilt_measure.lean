-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_tilt_measure
-- name    : AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:10:31.706791+00:00
-- url     : https://prove2.me/theorems/2d3eebc6-c8dd-41f7-9dbd-4dbe77bbbb42
-- title:
--   Exponential change of measure shifts a centred Gaussian law
-- statement:
--   If X is distributed as a centred Gaussian with positive variance v, weighting its law by exp(theta*x-v*theta²/2) produces exactly Gaussian(mean=v*theta,variance=v). The theorem is an equality of probability measures using the Mathlib withDensity construction, not merely an equality of densities. It is a substantive one-increment consequence used to derive Girsanov Brownian-law transfer under a constant deterministic drift. Process-level independence and filtration adaptation remain separate.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, Girsanov theorem and Gaussian Esscher transform.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem AppliedSDE.SarkkaSolin.gaussian_esscher_tilt_measure
    (v : ℝ≥0) (hv : 0 < v) (theta : ℝ) :
    (gaussianReal 0 v).withDensity
      (fun x : ℝ => ENNReal.ofReal
        (Real.exp (theta * x - (v : ℝ) * theta ^ 2 / 2))) =
      gaussianReal ((v : ℝ) * theta) v := by
  sorry
