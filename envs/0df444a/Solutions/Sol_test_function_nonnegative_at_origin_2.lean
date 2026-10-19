-- Prove2me | solution 2 for test_function_nonnegative_at_origin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:49.743617+00:00
-- url     : https://prove2.me/submissions/428fc326-10cf-40dc-8498-1e63d7fffcfe

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
include hCohnElkies₂


theorem solution : 0 ≤ (f 0).re := by
  have hinversion :
      (∫ x : EuclideanSpace ℝ (Fin d), (𝓕 f) x) = f 0 := by
    have h := congrArg (fun g : CohnElkies.TestFunction d => g 0)
      (show (𝓕⁻ (𝓕 f) : CohnElkies.TestFunction d) = f from
        FourierTransform.fourierInv_fourier_eq f)
    simpa only [CohnElkies.fourierInv_apply_zero] using! h
  rw [← hinversion]
  exact le_of_le_of_eq (integral_nonneg fun x => hCohnElkies₂ x) (integral_re (𝓕 f).integrable)

