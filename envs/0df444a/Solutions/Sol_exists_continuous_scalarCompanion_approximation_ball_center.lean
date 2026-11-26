-- Prove2me | solution 1 for exists_continuous_scalarCompanion_approximation_ball_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:35.383888+00:00
-- url     : https://prove2.me/submissions/ecdb55c1-13ee-4269-938c-8bce8c564afe

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    ∃ (g : ℂ → ℂ) (r : ℕ → Polynomial ℂ),
      ContinuousOn g
          ((SmoothJordanDomain.ball c R hR).boundaryParam ''
            Icc (0 : ℝ) (2 * Real.pi)) ∧
      (∀ z ∈ Metric.closedBall c R,
        ‖g z‖ ≤ polynomialSupNorm p (Metric.closedBall c R)) ∧
      (∀ (j : ℕ) (z : ℂ), z ∈ Metric.closedBall c R →
        ‖Polynomial.eval z (r j) - g z‖ ≤ 1 / ((j : ℝ) + 1)) ∧
      crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR) g =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p := by
  refine ⟨
    crouzeixPolynomialScalarCompanionClosedExtension
      (SmoothJordanDomain.ball c R hR) p,
    fun _ ↦ Polynomial.C (star (Polynomial.eval c p)), ?_, ?_, ?_, ?_⟩
  · apply
      (continuousOn_crouzeixPolynomialScalarCompanionClosedExtension_ball_center
        c hR p).mono
    rintro z ⟨t, _ht, rfl⟩
    exact circleMap_mem_closedBall c hR.le t
  · intro z hz
    rw [crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
      c hR p hz, norm_star]
    exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
      (Metric.mem_closedBall_self hR.le)
  · intro j z hz
    rw [Polynomial.eval_C,
      crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
        c hR p hz,
      sub_self, norm_zero]
    positivity
  · exact
      crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
        A c hR hA p
