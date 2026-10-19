-- Prove2me | solution 1 for test_function_nonnegative_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/c1d03f98-18d9-4317-b2df-e936f6616a63

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_fourier_transform_is_integrable

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
include hCohnElkies₂
theorem _root_.solution : 0 ≤ (f 0).re := by
  rw [← f.schwartz_fourier_inverse_identity, fourierInv_eq]
  simp only [inner_zero_right, AddChar.map_zero_eq_one, one_smul]
  rw [← RCLike.re_eq_complex_re, ← integral_re fourier_transform_is_integrable]
  refine integral_nonneg ?_
  intro v
  simpa [RCLike.re_eq_complex_re] using! hCohnElkies₂ v
