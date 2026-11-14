-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_two_increment_measure
-- name    : AppliedSDE.SarkkaSolin.gaussian_esscher_two_increment_measure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:19:37.646185+00:00
-- url     : https://prove2.me/theorems/cbdddcfd-01f5-41f8-b936-b8ec19d52048
-- title:
--   Girsanov Gaussian tilt preserves independence of two increments
-- statement:
--   For two independent centred Gaussian variables with positive variances v and w, weighting their product law by the product of exponential likelihood factors exp(theta x-v theta²/2) and exp(theta y-w theta²/2) yields the product law of independent Gaussian variables with respective means v theta and w theta. This is a rigorous finite-dimensional independence step in the deterministic-drift Girsanov argument, derived from the single-increment Gaussian tilt measure theorem and product measures.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7, Girsanov theorem.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussian_esscher_two_increment_measure
    (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w) (theta : ℝ) :
    ((gaussianReal 0 v).prod (gaussianReal 0 w)).withDensity
      (fun z : ℝ × ℝ =>
        ENNReal.ofReal
          (Real.exp (theta * z.1 - (v : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * z.2 - (w : ℝ) * theta ^ 2 / 2))) =
    (gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w) := by
  sorry
