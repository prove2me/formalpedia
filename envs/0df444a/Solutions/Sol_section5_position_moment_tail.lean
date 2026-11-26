-- Prove2me | solution 1 for section5_position_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:04:38.632157+00:00
-- url     : https://prove2.me/submissions/2b56cfc1-60d1-432d-a7b0-8219ad3f9b1b

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
theorem solution {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (R : ℝ) (hR : 0 ≤ R)
    (hf : Integrable (fun x => ‖f x‖^2))
    (hm : Integrable (fun x => x^2*‖f x‖^2)) :
    R^2 * (∫ x in {x : ℝ | R ≤ |x|}, ‖f x‖^2) ≤
      ∫ x : ℝ, x^2*‖f x‖^2 := by
  have hs : MeasurableSet {x : ℝ | R ≤ |x|} :=
    measurableSet_le measurable_const measurable_id.abs
  rw [← integral_const_mul]
  calc
    _ ≤ ∫ x in {x : ℝ | R ≤ |x|}, x^2*‖f x‖^2 := by
      apply setIntegral_mono_on ((hf.const_mul _).integrableOn) hm.integrableOn hs
      intro x hx
      have hsq : R^2 ≤ x^2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ hR hx 2
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ ≤ _ := setIntegral_le_integral hm (Filter.Eventually.of_forall
      (fun x => mul_nonneg (sq_nonneg x) (sq_nonneg ‖f x‖)))
