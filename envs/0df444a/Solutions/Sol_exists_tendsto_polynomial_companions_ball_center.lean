-- Prove2me | solution 1 for exists_tendsto_polynomial_companions_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:37.506865+00:00
-- url     : https://prove2.me/submissions/e6e401db-37ce-4064-a140-bbae6bd34953

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm
import Theorems.Thm_polynomialSupNorm_C_of_nonempty


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ∃ q : ℕ → Polynomial ℂ,
      (∀ j, polynomialSupNorm (q j) (Metric.closedBall c R) ≤
        polynomialSupNorm p (Metric.closedBall c R)) ∧
      Tendsto (fun j ↦ Polynomial.aeval A (q j)) atTop
        (nhds (crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p)) := by
  refine ⟨fun _ ↦ Polynomial.C (star (Polynomial.eval c p)), ?_, ?_⟩
  · intro _
    rw [polynomialSupNorm_C_of_nonempty _
      (Metric.nonempty_closedBall.mpr hR.le), norm_star]
    exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
      (Metric.mem_closedBall_self hR.le)
  · rw [←
      aeval_C_star_eval_center_eq_crouzeixPolynomialAuxiliaryOperator_ball_center
        A c hR hA p]
    exact tendsto_const_nhds
