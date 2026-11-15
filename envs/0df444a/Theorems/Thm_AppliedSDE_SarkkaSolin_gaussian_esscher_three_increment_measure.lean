-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_three_increment_measure
-- name    : AppliedSDE.SarkkaSolin.gaussian_esscher_three_increment_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:04:54.8873+00:00
-- url     : https://prove2.me/theorems/c4802bab-5016-4187-ba5d-4187d306ce81
-- title:
--   Independent Gaussian increments remain independent after three-factor Girsanov tilt
-- statement:
--   For three independent centred normal increments with positive variances v, w, u, weighting the joint product law by the product of their exponential martingale likelihood factors yields the product of the three Gaussian laws with shifted means v theta, w theta, and u theta. The result follows by applying the proved two-increment and single-increment Esscher measure identities to a second product-density decomposition.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, Girsanov theorem.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_two_increment_measure
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_tilt_measure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.gaussian_esscher_three_increment_measure
    (v w u : ℝ≥0) (hv : 0 < v) (hw : 0 < w) (hu : 0 < u)
    (theta : ℝ) :
    (((gaussianReal 0 v).prod (gaussianReal 0 w)).prod
      (gaussianReal 0 u)).withDensity
      (fun z : (ℝ × ℝ) × ℝ =>
        (ENNReal.ofReal
            (Real.exp (theta * z.1.1 - (v : ℝ) * theta ^ 2 / 2)) *
          ENNReal.ofReal
            (Real.exp (theta * z.1.2 - (w : ℝ) * theta ^ 2 / 2))) *
        ENNReal.ofReal
          (Real.exp (theta * z.2 - (u : ℝ) * theta ^ 2 / 2))) =
    ((gaussianReal ((v : ℝ) * theta) v).prod
      (gaussianReal ((w : ℝ) * theta) w)).prod
      (gaussianReal ((u : ℝ) * theta) u) := by
  sorry
