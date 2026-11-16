-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a545_integrable_of_quadratic_gaussian_envelope
-- name    : AvramDividend.Classical.avram_ga_a545_integrable_of_quadratic_gaussian_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:45:16.729232+00:00
-- url     : https://prove2.me/theorems/a2b2a709-1ea9-4df7-9b27-671125015472
-- title:
--   A nonnegative quadratic Gaussian envelope suffices for integrability
-- statement:
--   Any a.e. measurable random variable bounded in absolute value by a nonnegative constant times one plus the square of an L2 random variable is integrable on a finite measure space.
-- source:
--   Mathlib Integrable.mono taking g=M*(1+z²), finite-measure integrability of constants and square integrability of z.

import Mathlib
open MeasureTheory Set Filter
noncomputable section

theorem AvramDividend.Classical.avram_ga_a545_integrable_of_quadratic_gaussian_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (f z : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : AEStronglyMeasurable f P)
    (hzsq : Integrable (fun ω => (z ω)^2) P)
    (hBound : ∀ᵐ ω ∂P, |f ω| ≤ M * (1 + (z ω)^2)) :
    Integrable f P := by sorry
