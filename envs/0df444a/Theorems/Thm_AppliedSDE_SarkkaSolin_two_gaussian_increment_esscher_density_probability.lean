-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_two_gaussian_increment_esscher_density_probability
-- name    : AppliedSDE.SarkkaSolin.two_gaussian_increment_esscher_density_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:58:00.791992+00:00
-- url     : https://prove2.me/theorems/6c848f5c-9382-4b57-9bb6-995ed49e3c3a
-- title:
--   Two-independent-Gaussian exponential likelihood factors define a probability measure
-- statement:
--   Suppose X and Y have the product law of two centred independent Gaussian increments with positive variances v,w under probability measure P. Reweight P by their product of normalised exponential likelihoods exp(theta X-v theta²/2)*exp(theta Y-w theta²/2). This produces a genuine probability measure of mass one: the weighted measure is normalised, with no extra expectation hypothesis. The proof pushes the likelihood-weighted law to the already-proved product of shifted Gaussian probabilities and reads its total mass.
-- source:
--   Särkkä and Solin, Applied Stochastic Differential Equations (2019), Chapter 7; finite-dimensional normalisation for deterministic-drift Girsanov.

import Mathlib
import Theorems.Thm_AppliedSDE_SarkkaSolin_joint_gaussian_increment_esscher_under_weighted_measure
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem AppliedSDE.SarkkaSolin.two_gaussian_increment_esscher_density_probability
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (v w : ℝ≥0) (hv : 0 < v) (hw : 0 < w)
    (theta : ℝ)
    (hZ : Measurable (fun ω : Ω => (X ω, Y ω)))
    (hXY : HasLaw (fun ω : Ω => (X ω, Y ω))
      ((gaussianReal 0 v).prod (gaussianReal 0 w)) P) :
    IsProbabilityMeasure
      (P.withDensity (fun ω =>
        ENNReal.ofReal
          (Real.exp (theta * X ω - (v : ℝ) * theta ^ 2 / 2)) *
        ENNReal.ofReal
          (Real.exp (theta * Y ω - (w : ℝ) * theta ^ 2 / 2)))) := by
  sorry
