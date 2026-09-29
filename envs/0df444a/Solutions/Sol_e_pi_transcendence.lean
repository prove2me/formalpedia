-- Prove2me | solution 1 for e_pi_transcendence
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T18:03:57.333869+00:00
-- url     : https://prove2.me/submissions/fd9af761-c9c6-45a8-9d08-7e334384744c

import Mathlib
import Theorems.Thm_Schanuel_gelfond_schneider

namespace P17_epi

theorem isAlgebraic_neg_I : IsAlgebraic ℚ (-Complex.I) := by
  refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
  · intro h
    have h0 := congrArg (Polynomial.eval 0) h
    simp at h0
  · simp

theorem neg_I_ne_rat (q : ℚ) : -Complex.I ≠ (q : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp at him

theorem isAlgebraic_exp_pi_mul_I :
    IsAlgebraic ℚ (Complex.exp (((Real.pi : ℝ) : ℂ) * Complex.I)) := by
  rw [Complex.exp_pi_mul_I]
  have h : ((-1 : ℚ) : ℂ) = -1 := by push_cast; ring
  rw [← h]
  exact isAlgebraic_algebraMap (-1 : ℚ)

theorem pi_mul_I_ne_zero : ((Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero) Complex.I_ne_zero

theorem neg_I_mul_pi_mul_I :
    -Complex.I * (((Real.pi : ℝ) : ℂ) * Complex.I) = ((Real.pi : ℝ) : ℂ) := by
  have h : -Complex.I * (((Real.pi : ℝ) : ℂ) * Complex.I)
      = -(((Real.pi : ℝ) : ℂ) * (Complex.I * Complex.I)) := by ring
  rw [h, Complex.I_mul_I]
  ring

end P17_epi

open P17_epi in
theorem solution :
    Transcendental ℚ (Real.exp Real.pi) := by
  have h := Schanuel.gelfond_schneider (-Complex.I) (((Real.pi : ℝ) : ℂ) * Complex.I)
    isAlgebraic_neg_I neg_I_ne_rat isAlgebraic_exp_pi_mul_I pi_mul_I_ne_zero
  rw [neg_I_mul_pi_mul_I, ← Complex.ofReal_exp] at h
  exact (transcendental_algebraMap_iff (algebraMap ℝ ℂ).injective).mp h

#print axioms solution
