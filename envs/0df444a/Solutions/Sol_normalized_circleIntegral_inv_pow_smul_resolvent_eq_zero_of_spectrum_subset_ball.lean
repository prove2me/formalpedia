-- Prove2me | solution 1 for normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:41:11.247307+00:00
-- url     : https://prove2.me/submissions/e34b2f1f-9af1-4b73-ac33-ffa110baa8f4

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball
import Theorems.Thm_normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r)
    (n : ℕ) (hn : 0 < n) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => z⁻¹ ^ n • resolvent A z) 0 r = 0 := by
  have hR : ‖A‖ < ‖A‖ + r := by linarith
  have hg : ∀ z : ℂ, z ∉ Metric.ball (0 : ℂ) r → DifferentiableAt ℂ (fun z : ℂ => z⁻¹ ^ n) z := by
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hz (Metric.mem_ball_self hr)
    exact (differentiableAt_inv hz0).pow n
  rw [circleIntegral_smul_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg A] : r ≤ ‖A‖ + r) hσ hg]
  exact normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero A hR n hn
