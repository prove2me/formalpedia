-- Prove2me | solution 1 for normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:27.156533+00:00
-- url     : https://prove2.me/submissions/23250754-493a-4d2f-8c89-c2d8cab798ce

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt

set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c r = aeval A p := by
  have hR : ‖A - c • (1 : E →L[ℂ] E)‖ < ‖A - c • (1 : E →L[ℂ] E)‖ + r := by linarith
  rw [circleIntegral_eval_smul_resolvent_eq_of_spectrum_subset_ball A hr
    (by linarith [norm_nonneg (A - c • (1 : E →L[ℂ] E))] :
      r ≤ ‖A - c • (1 : E →L[ℂ] E)‖ + r) hσ p]
  exact normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt A c hR p
