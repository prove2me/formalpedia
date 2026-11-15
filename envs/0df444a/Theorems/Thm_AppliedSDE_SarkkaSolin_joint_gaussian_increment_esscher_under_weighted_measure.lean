-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_joint_gaussian_increment_esscher_under_weighted_measure
-- name    : AppliedSDE.SarkkaSolin.joint_gaussian_increment_esscher_under_weighted_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:44:52.878775+00:00
-- url     : https://prove2.me/theorems/c35c51c4-ac07-4368-82ef-91e777ee262a
-- title:
--   Joint independent Gaussian increment law after weighting the underlying probability space
-- statement:
--   Suppose two real random variables X and Y have independent centred Gaussian laws of variances v,w>0 under a probability measure P. Change P by the product of their exponential likelihood ratios exp(theta X-v theta²/2) exp(theta Y-w theta²/2), and push the weighted law forward through (X,Y). The resulting joint law is the product of independent Gaussian distributions with means v theta and w theta, and the same respective variances. This transports the proved two-increment Gaussian Esscher identity to arbitrary probability spaces and provides a directly reusable finite-dimensional deterministic-drift Girsanov theorem for Brownian increments.
-- source:
--   Sarkka and Solin (2019), Applied Stochastic Differential Equations, Chapter 7: joint Gaussian change of measure.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_likelihood_tilt_pushforward
import Theorems.Thm_AppliedSDE_SarkkaSolin_gaussian_esscher_two_increment_measure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.joint_gaussian_increment_esscher_under_weighted_measure
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w)
    (theta : ℝ)
    (hZ : Measurable (fun ω : Ω => (X ω, Y ω)))
    (hXY : HasLaw (fun ω : Ω => (X ω, Y ω))
      ((gaussianReal 0 v).prod (gaussianReal 0 w)) P) :
    (P.withDensity (fun ω =>
        ENNReal.ofReal
          (Real.exp (theta * X ω - (v : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * Y ω - (w : ℝ) * theta ^ 2 / 2)))).map
        (fun ω : Ω => (X ω, Y ω)) =
      (gaussianReal ((v : ℝ) * theta) v).prod
        (gaussianReal ((w : ℝ) * theta) w) := by
  sorry
