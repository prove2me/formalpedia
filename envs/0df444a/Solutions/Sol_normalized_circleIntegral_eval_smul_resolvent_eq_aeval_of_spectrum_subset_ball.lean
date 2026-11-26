-- Prove2me | solution 1 for normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:45:12.871163+00:00
-- url     : https://prove2.me/submissions/1ed116d5-6835-47ac-873b-8d6a510371e2

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval


set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r)
    (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) 0 r = aeval A p := by
  have hR : ‖A‖ < ‖A‖ + r := by linarith
  rw [circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg A] : r ≤ ‖A‖ + r) hσ p]
  exact normalized_circleIntegral_eval_smul_resolvent_eq_aeval A hR p
