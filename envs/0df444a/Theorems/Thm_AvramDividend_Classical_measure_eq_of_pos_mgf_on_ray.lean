-- Prove2me | Theorems.Thm_AvramDividend_Classical_measure_eq_of_pos_mgf_on_ray
-- name    : AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:14:33.43299+00:00
-- url     : https://prove2.me/theorems/4fb183cd-2d4f-4df5-8a23-9c6e5b201da0
-- title:
--   Probability measures are determined by all positive exponential moments
-- statement:
--   Two probability measures on the real line with finite exponential moments at every positive parameter are equal when those moments agree at every positive parameter. The intended proof continues the complex moment-generating functions analytically on the right half-plane, takes the dominated boundary limit to characteristic functions, and applies the pinned finite-measure characteristic-function uniqueness theorem. This isolates the exact increment-law uniqueness step needed for the bounded-variation stopped-scale balance target 2bb529c8-d611-4c49-9460-1d4af4620ae8.
-- source:
--   Source-faithful measure-uniqueness prerequisite for identifying actual Esscher-loss increments with the positive countable-band compound-Poisson limit. It uses the Proved actual-process BV Laplace transform and the Proved finite-band compound-Poisson PGF helpers; it does not assert a stopped-exit law or close the parent target by publication alone.

import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory ProbabilityTheory Filter Set
open Complex

theorem AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ s : ℝ, 0 < s → Integrable (fun x : ℝ => Real.exp (s * x)) μ)
    (hν : ∀ s : ℝ, 0 < s → Integrable (fun x : ℝ => Real.exp (s * x)) ν)
    (hm : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (s * x) ∂μ) = ∫ x, Real.exp (s * x) ∂ν) : μ = ν := by sorry
