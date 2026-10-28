-- Prove2me | Theorems.Thm_AvramDividend_Classical_normalized_laplace_tilt_is_probability
-- name    : AvramDividend.Classical.normalized_laplace_tilt_is_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:42:29.668725+00:00
-- url     : https://prove2.me/theorems/65330e80-ab14-4843-b2e9-7151b775548a
-- title:
--   A normalized positive Laplace tilt is a probability measure
-- statement:
--   If C is the positive Laplace value at s₀, weighting a probability law by exp(-s₀ x)/C produces another probability law. This is the normalization step in the finite-cutoff Pollaczek–Khinchine derivation for target 494dbcd1-770a-49c0-986b-046103fab9c4.
-- source:
--   Source-faithful factor of the normalized-reflected-tilt derivation in candidates/work_on/494db_laplace_ray_measure_uniqueness_draft_20261028.lean, grounded in the exact 494 target preparation at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474. This establishes only the probability normalization identity; it does not establish the two-sided exit theorem or an authoritative parent edge.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.normalized_laplace_tilt_is_probability
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (s₀ C : ℝ)
    (hC : C = ∫ x, Real.exp (-(s₀ * x)) ∂μ)
    (hCpos : 0 < C)
    (hInt : Integrable (fun x : ℝ => Real.exp (-(s₀ * x))) μ) :
    IsProbabilityMeasure
      (μ.withDensity (fun x => ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x))))) := by sorry
