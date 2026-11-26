-- Prove2me | solution 1 for normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_norm_sub_smul_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:39.02412+00:00
-- url     : https://prove2.me/submissions/e4604639-2e84-4441-b85a-37f574cb000b

import Mathlib.Analysis.Complex.CauchyIntegral
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleSymmetrized
import Definitions.Def_Operator_Crouzeix_AffinePolynomial
import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Theorems.Thm_circleIntegral_eval_smul_resolvent_eq_center
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval
attribute [local simp] Polynomial.aeval_affineComposition



set_option autoImplicit false
open Complex Polynomial spectrum
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : ℂ[X]) :
    (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z : ℂ => p.eval z • resolvent A z) c R = aeval A p := by
  rw [circleIntegral_eval_smul_resolvent_eq_center,
    normalized_circleIntegral_eval_smul_resolvent_eq_aeval (A - c • (1 : E →L[ℂ] E)) hA,
    aeval_affineComposition, one_smul, sub_add_cancel]
