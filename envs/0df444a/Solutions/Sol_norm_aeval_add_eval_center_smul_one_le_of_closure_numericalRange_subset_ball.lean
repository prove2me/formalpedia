-- Prove2me | solution 1 for norm_aeval_add_eval_center_smul_one_le_of_closure_numericalRange_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:30.638952+00:00
-- url     : https://prove2.me/submissions/3e8d9146-58c8-421d-b38b-f24f86bfc881

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
import Theorems.Thm_norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball_center
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hW : closure (numericalRange A) ⊆ Metric.ball c r) (p : ℂ[X]) :
    ‖aeval A p + (p.eval c) • (1 : E →L[ℂ] E)‖ ≤
      2 * polynomialSupNorm p (Metric.closedBall c r) := by
  have hσ : spectrum ℂ A ⊆ Metric.ball c r :=
    (spectrum_subset_closure_numericalRange A).trans hW
  have h := norm_aeval_add_star_crouzeixPolynomialAuxiliaryOperator_ball_le_of_closure_numericalRange_subset_ball_center
    A hr hW p
  rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one_of_spectrum_subset_ball
    A c hr hσ p, star_smul, star_one, star_star] at h
  exact h
