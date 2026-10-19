-- Prove2me | solution 2 for test_function_positive_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:18.902944+00:00
-- url     : https://prove2.me/submissions/4d572deb-6951-44ad-9e72-a46b3d18bfd9

import Mathlib
import Definitions.Def_SpherePacking
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


theorem solution : 0 < (f 0).re := by
  obtain ⟨x0, hx0⟩ : ∃ x, (𝓕 f x).re ≠ 0 := by
    by_contra h
    push_neg at h
    apply hne_zero
    have h0 : 𝓕 f = 0 := by
      ext x
      rw [← hRealFourier x, h x]
      simp
    have hf : (𝓕⁻ (𝓕 f) : CohnElkies.TestFunction d) = f := FourierTransform.fourierInv_fourier_eq f
    calc f = 𝓕⁻ (𝓕 f) := hf.symm
      _ = 0 := by rw [h0, FourierTransform.fourierInv_zero]
  have hpositive : 0 < ∫ x : EuclideanSpace ℝ (Fin d), ((𝓕 f) x).re := by
    exact integral_pos_of_integrable_nonneg_nonzero
      (Complex.continuous_re.comp (𝓕 f).continuous)
      (𝓕 f).integrable.re
      (fun x => hCohnElkies₂ x) hx0
  have hinversion :
      (∫ x : EuclideanSpace ℝ (Fin d), (𝓕 f) x) = f 0 := by
    have h := congrArg (fun g : CohnElkies.TestFunction d => g 0)
      (show (𝓕⁻ (𝓕 f) : CohnElkies.TestFunction d) = f from
        FourierTransform.fourierInv_fourier_eq f)
    simpa only [CohnElkies.fourierInv_apply_zero] using! h
  calc
    (0 : ℝ) < (∫ x : EuclideanSpace ℝ (Fin d), ((𝓕 f) x).re) := hpositive
    _ = (∫ x : EuclideanSpace ℝ (Fin d), (𝓕 f) x).re :=
      integral_re (𝓕 f).integrable
    _ = (f 0).re := congrArg Complex.re hinversion

