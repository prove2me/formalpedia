-- Prove2me | solution 1 for thm_6_5
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T09:36:50.290726+00:00
-- url     : https://prove2.me/submissions/58bae15b-e8ae-4df9-9fc1-4372b9536308

import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open MeasureTheory


/-- ## Theorem 6.5: linearity of the Lebesgue integral for nonnegative measurable functions.

We prove this using existing theorems in Mathlib
-/
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hX : Measurable X) (_hY : Measurable Y) (c : ENNReal) :
    ∫⁻ ω, X ω + Y ω ∂μ = ∫⁻ ω, X ω ∂μ + ∫⁻ ω, Y ω ∂μ ∧
      ∫⁻ ω, c * X ω ∂μ = c * ∫⁻ ω, X ω ∂μ := by
  exact ⟨lintegral_add_left hX _, lintegral_const_mul c hX⟩

