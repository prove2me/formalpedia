-- Prove2me | Theorems.Thm_AvramDividend_Classical_normalized_laplace_tilt_reflected_mgf
-- name    : AvramDividend.Classical.normalized_laplace_tilt_reflected_mgf
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T13:42:34.310866+00:00
-- url     : https://prove2.me/theorems/183a502d-ed2d-4742-b023-5875006d0821
-- title:
--   The reflected Laplace tilt has the shifted positive MGF
-- statement:
--   For an integrable shifted Laplace moment, the positive MGF of the reflected exponentially tilted law is the original Laplace transform at s₀+t divided by C, and it is integrable. This isolates the change-of-variables and with-density calculation used by target 494dbcd1-770a-49c0-986b-046103fab9c4.
-- source:
--   Extracted from the reflected-tilt calculation in candidates/work_on/494db_laplace_ray_measure_uniqueness_draft_20261028.lean and the same-revision accepted withDensity integral identities used by the Proved measure_eq_of_pos_mgf_on_ray source. This lemma does not establish measure uniqueness or the two-sided exit identity.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AvramDividend.Classical.normalized_laplace_tilt_reflected_mgf
    {μ : Measure ℝ} (s₀ C t : ℝ)
    (hCpos : 0 < C) (ht : 0 < t)
    (hInt : Integrable (fun x : ℝ => Real.exp (-((s₀ + t) * x))) μ) :
    let μ₀ := μ.withDensity
      (fun x => ENNReal.ofReal (C⁻¹ * Real.exp (-(s₀ * x))))
    Integrable (fun y : ℝ => Real.exp (t * y)) (Measure.map (fun x : ℝ => -x) μ₀) ∧
      (∫ y, Real.exp (t * y) ∂(Measure.map (fun x : ℝ => -x) μ₀)) =
        C⁻¹ * ∫ x, Real.exp (-((s₀ + t) * x)) ∂μ := by sorry
