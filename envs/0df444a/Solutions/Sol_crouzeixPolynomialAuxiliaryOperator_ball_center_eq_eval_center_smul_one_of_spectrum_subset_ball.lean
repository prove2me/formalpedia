-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:04.478491+00:00
-- url     : https://prove2.me/submissions/7573f304-35a4-4380-99b8-00a66407083f

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_spectrum_sub_smul_one_subset_ball_of_subset_ball
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
attribute [local simp] Polynomial.eval_affineComposition



set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {r : ℝ} (hr : 0 < r) (hσ : spectrum ℂ A ⊆ Metric.ball c r)
    (p : ℂ[X]) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball c r hr) p =
      star (p.eval c) • (1 : E →L[ℂ] E) := by
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center A c hr p,
    crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
      (A - c • (1 : E →L[ℂ] E)) hr (spectrum_sub_smul_one_subset_ball_of_subset_ball A hσ),
    eval_affineComposition, one_mul, zero_add]
