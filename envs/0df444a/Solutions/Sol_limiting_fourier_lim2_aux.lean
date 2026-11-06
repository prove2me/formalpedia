-- Prove2me | solution 1 for limiting_fourier_lim2_aux
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:59.608203+00:00
-- url     : https://prove2.me/submissions/b591da5a-652c-4b13-ad24-8a673b1168ed

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Real MeasureTheory Set

theorem solution (x : ℝ) (C : ℝ) :
    Integrable (fun t ↦ max |x| 1 * (C / (1 + (t / (2 * π)) ^ 2)))
      (Measure.restrict volume (Ici (-Real.log x))) := by
  simp_rw [div_eq_mul_inv C]
  exact (((integrable_inv_one_add_sq.comp_div
    (by simp [pi_ne_zero])).const_mul _).const_mul _).restrict
