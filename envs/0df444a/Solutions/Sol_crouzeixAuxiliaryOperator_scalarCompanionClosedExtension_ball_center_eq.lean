-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_ball_center_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:54:51.410828+00:00
-- url     : https://prove2.me/submissions/9429409d-60ee-4a2c-8a05-5c666d172617

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hA : ‖A - c • (1 : E →L[ℂ] E)‖ < R) (p : Polynomial ℂ) :
    crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
        (crouzeixPolynomialScalarCompanionClosedExtension
          (SmoothJordanDomain.ball c R hR) p) =
      crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball c R hR) p := by
  let q : Polynomial ℂ := Polynomial.C (Polynomial.eval c p)
  have hclosedAux :
      crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
          (crouzeixPolynomialScalarCompanionClosedExtension
            (SmoothJordanDomain.ball c R hR) p) =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) q := by
    unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
    congr 1
    unfold contourIntegral
    apply intervalIntegral.integral_congr
    intro t _
    change deriv (circleMap c R) t •
        (crouzeixPolynomialScalarCompanionClosedExtension
            (SmoothJordanDomain.ball c R hR) p (circleMap c R t) •
          resolvent A (circleMap c R t)) =
      deriv (circleMap c R) t •
        (star (Polynomial.eval (circleMap c R t) q) •
          resolvent A (circleMap c R t))
    rw [crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
      c hR p (circleMap_mem_closedBall c hR.le t)]
    simp only [q, Polynomial.eval_C]
  calc
    crouzeixAuxiliaryOperator A (SmoothJordanDomain.ball c R hR)
        (crouzeixPolynomialScalarCompanionClosedExtension
          (SmoothJordanDomain.ball c R hR) p) =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) q := hclosedAux
    _ = star (Polynomial.eval c p) • (1 : E →L[ℂ] E) := by
      simpa only [q, Polynomial.eval_C] using
        (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
          A c hA q)
    _ = crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p := by
      symm
      simpa using
        (crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
          A c hA p)
