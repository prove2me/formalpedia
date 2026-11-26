-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:40.546794+00:00
-- url     : https://prove2.me/submissions/80f9c9e8-616e-4d18-91b9-c984911b49e4

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z =
      star (Polynomial.eval c p) := by
  let A : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ z
  have hAc : ‖A - c • (1 : ℂ →L[ℂ] ℂ)‖ < R := by
    have heq : A - c • (1 : ℂ →L[ℂ] ℂ) =
        ContinuousLinearMap.toSpanSingleton ℂ (z - c) := by
      apply ContinuousLinearMap.ext
      intro x
      change x * z - c * x = x * (z - c)
      ring
    rw [heq, ContinuousLinearMap.norm_toSpanSingleton]
    simpa only [Metric.mem_ball, dist_eq_norm] using hz
  calc
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z =
        crouzeixPolynomialAuxiliaryOperator A
          (SmoothJordanDomain.ball c R hR) p 1 :=
      crouzeixPolynomialScalarCompanion_eq_auxiliaryOperator_apply_one
        (SmoothJordanDomain.ball c R hR) p hz
    _ = (star (Polynomial.eval c p) • (1 : ℂ →L[ℂ] ℂ)) 1 := by
      rw [crouzeixPolynomialAuxiliaryOperator_ball_center_eq_eval_center_smul_one
        A c hAc p]
    _ = star (Polynomial.eval c p) := by
      change star (Polynomial.eval c p) * (1 : ℂ) = _
      rw [mul_one]
