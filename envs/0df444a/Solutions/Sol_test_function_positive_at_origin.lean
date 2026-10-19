-- Prove2me | solution 1 for test_function_positive_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/f5a7536c-c2c1-466c-8ee3-298dfd8544f3

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_Continuous_nonnegative_integral_vanishes_iff_function_vanishes
import Theorems.Thm_fourier_transform_is_integrable
import Theorems.Thm_fourier_transform_nonzero
import Theorems.Thm_test_function_nonnegative_at_origin

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
open scoped FourierTransform ENNReal SchwartzMap BigOperators
open SpherePacking MeasureTheory Complex Real Bornology Module
variable {d : ℕ}
variable {f : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)} (hne_zero : f ≠ 0)
variable (hReal : ∀ x : EuclideanSpace ℝ (Fin d), ↑(f x).re = (f x))
variable (hRealFourier : ∀ x : EuclideanSpace ℝ (Fin d), ↑(𝓕 f x).re = (𝓕 f x))
variable (hCohnElkies₁ : ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≥ 1 → (f x).re ≤ 0)
variable (hCohnElkies₂ : ∀ x : EuclideanSpace ℝ (Fin d), (𝓕 f x).re ≥ 0)
include hReal hRealFourier hCohnElkies₂ hne_zero
theorem _root_.solution : 0 < (f 0).re := by
  have h0 : 0 ≤ (f 0).re := test_function_nonnegative_at_origin (f := f) hCohnElkies₂
  refine lt_of_le_of_ne h0 ?_
  intro hf0re
  have hf0 : f 0 = 0 := by
    simpa [hf0re.symm] using! (hReal 0).symm
  have hint0 : (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v) = 0 := by
    have hInv : 𝓕⁻ (𝓕 ⇑f) 0 = f 0 :=
      congrArg (fun g : EuclideanSpace ℝ (Fin d) → ℂ => g 0) (f.schwartz_fourier_inverse_identity)
    simpa [fourierInv_eq, inner_zero_right, AddChar.map_zero_eq_one, one_smul, hf0] using! hInv
  have hintRe : ∫ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).re = 0 := by
    have : (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re = 0 := by
      simpa using! congrArg Complex.re hint0
    have hre :
        (∫ v : EuclideanSpace ℝ (Fin d), (𝓕 (⇑f) v).re) =
          (∫ v : EuclideanSpace ℝ (Fin d), 𝓕 (⇑f) v).re := by
      simpa using!
        (integral_re (f := fun v : EuclideanSpace ℝ (Fin d) => 𝓕 (⇑f) v) fourier_transform_is_integrable)
    exact hre.trans this
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin d) => (𝓕 f x).re) := by
    fun_prop
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => (𝓕 f x).re) = 0 := by
    refine (Continuous.nonnegative_integral_vanishes_iff_function_vanishes hcont ?_ hCohnElkies₂).1 ?_
    · have h𝓕_int : MeasureTheory.Integrable
          (fun x : EuclideanSpace ℝ (Fin d) => 𝓕 f x) := by
        rw [← FourierTransform.fourierCLE_apply (R := ℝ)
          (E := 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) f]
        exact ((FourierTransform.fourierCLE ℝ (SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ)) f).integrable
      exact h𝓕_int.re
    simpa using! hintRe
  have h𝓕fzero : 𝓕 f = 0 := by
    ext x
    have hx : (𝓕 f x).re = 0 := by simpa [hfun] using! congrArg (fun g => g x) hfun
    simpa [hx] using! (hRealFourier x).symm
  exact fourier_transform_nonzero hne_zero h𝓕fzero
