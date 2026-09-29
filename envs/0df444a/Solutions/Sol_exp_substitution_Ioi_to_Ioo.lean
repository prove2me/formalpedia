-- Prove2me | solution 1 for exp_substitution_Ioi_to_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T19:34:12.666981+00:00
-- url     : https://prove2.me/submissions/21c3d5a8-701a-4fb1-94fd-c465ea518c48

import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
open MeasureTheory Set

theorem solution (lam : ℝ) (hlam : 0 < lam) (g : ℝ → ℝ) :
    ∫ t in Ioi (0:ℝ), |lam * Real.exp (-(lam * t))| * g (1 - Real.exp (-(lam * t)))
      = ∫ u in Ioo (0:ℝ) 1, g u := by
  set f : ℝ → ℝ := fun t => 1 - Real.exp (-(lam * t)) with hf
  set f' : ℝ → ℝ := fun t => lam * Real.exp (-(lam * t)) with hf'
  -- f '' Ioi 0 = Ioo 0 1
  have himg : f '' Ioi 0 = Ioo (0:ℝ) 1 := by
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [mem_Ioi] at ht
      simp only [hf, mem_Ioo]
      have he : (0:ℝ) < Real.exp (-(lam * t)) := Real.exp_pos _
      have he1 : Real.exp (-(lam * t)) < 1 := by
        rw [Real.exp_lt_one_iff]; nlinarith [ht, hlam]
      constructor <;> linarith
    · intro hy
      rw [mem_Ioo] at hy
      obtain ⟨hy0, hy1⟩ := hy
      -- t = -log(1-y)/lam
      refine ⟨-(Real.log (1 - y)) / lam, ?_, ?_⟩
      · rw [mem_Ioi]
        have h1y : (0:ℝ) < 1 - y := by linarith
        have hlog : Real.log (1 - y) < 0 := Real.log_neg h1y (by linarith)
        rw [div_pos_iff]; left; constructor <;> [linarith; linarith]
      · simp only [hf]
        have h1y : (0:ℝ) < 1 - y := by linarith
        rw [show -(lam * (-(Real.log (1 - y)) / lam)) = Real.log (1 - y) by field_simp]
        rw [Real.exp_log h1y]; ring
  -- HasDerivWithinAt on Ioi 0
  have hderiv : ∀ t ∈ Ioi (0:ℝ), HasDerivWithinAt f (f' t) (Ioi 0) t := by
    intro t _
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (-(lam * s)))
        (Real.exp (-(lam * t)) * (-lam)) t := by
      have hinner : HasDerivAt (fun s : ℝ => -(lam * s)) (-lam) t :=
        ((hasDerivAt_id t).const_mul lam).neg.congr_deriv (by ring)
      exact hinner.exp
    have hF : HasDerivAt f (f' t) t := by
      show HasDerivAt (fun t => 1 - Real.exp (-(lam * t))) (lam * Real.exp (-(lam * t))) t
      exact (hexp.const_sub 1).congr_deriv (by ring)
    exact hF.hasDerivWithinAt
  -- InjOn
  have hinj : InjOn f (Ioi 0) := by
    intro a _ b _ hab
    simp only [hf] at hab
    have : Real.exp (-(lam * a)) = Real.exp (-(lam * b)) := by linarith
    have h2 : -(lam * a) = -(lam * b) := Real.exp_injective this
    have : lam * a = lam * b := by linarith
    exact mul_left_cancel₀ (by linarith : lam ≠ 0) this
  have hmeas : MeasurableSet (Ioi (0:ℝ)) := measurableSet_Ioi
  have key := integral_image_eq_integral_abs_deriv_smul hmeas hderiv hinj g
  rw [himg] at key
  rw [key]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [hf, hf', smul_eq_mul]
