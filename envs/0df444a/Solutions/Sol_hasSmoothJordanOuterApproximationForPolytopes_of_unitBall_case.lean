-- Prove2me | solution 1 for hasSmoothJordanOuterApproximationForPolytopes_of_unitBall_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:10:50.587138+00:00
-- url     : https://prove2.me/submissions/07e02e7c-1110-47f9-8d91-a47c782cbeea

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
import Theorems.Thm_complexMulRealEquiv_apply
import Theorems.Thm_HasSmoothJordanOuterApproximation_homothety
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam
import Theorems.Thm_SmoothJordanDomain_ellipse_boundaryParam_deriv
import Theorems.Thm_SmoothJordanDomain_ellipse_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_apply
import Theorems.Thm_SmoothJordanDomain_translate_boundaryParam_deriv
import Theorems.Thm_SmoothJordanDomain_translate_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_deriv
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_boundaryParam_outwardNormal
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_closure_carrier
import Theorems.Thm_StrictNestedSmoothJordanExhaustion_closedBall_domain_frontier_carrier
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.ellipse_boundaryParam
attribute [local simp] SmoothJordanDomain.ellipse_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.ellipse_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.translate_boundaryParam
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_apply
attribute [local simp] SmoothJordanDomain.translate_boundaryParam_deriv
attribute [local simp] SmoothJordanDomain.translate_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_deriv
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_boundaryParam_outwardNormal
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_closure_carrier
attribute [local simp] StrictNestedSmoothJordanExhaustion.closedBall_domain_frontier_carrier
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] complexMulRealEquiv_apply

set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    (hunit : HasSmoothJordanOuterApproximationForUnitBallPolytopes) :
    HasSmoothJordanOuterApproximationForPolytopes := by
  intro u hPinterior
  let P : Set ℂ := convexHull ℝ (u : Set ℂ)
  obtain ⟨c, hcP⟩ := hPinterior
  obtain ⟨r, hr, hballP⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp hcP)
  let s : ℝ := r / 2
  have hs : 0 < s := by
    dsimp only [s]
    linarith
  let f : ℂ →ᵃ[ℝ] ℂ := AffineMap.homothety c s⁻¹
  let v : Finset ℂ := u.image f
  let Q : Set ℂ := convexHull ℝ (v : Set ℂ)
  have hQimage : Q = f '' P := by
    dsimp only [Q, v, P]
    rw [Finset.coe_image, ← f.image_convexHull]
  have hunitQ : Metric.closedBall c 1 ⊆ Q := by
    intro z hz
    rw [hQimage]
    let y : ℂ := AffineMap.homothety c s z
    have hyBall : y ∈ Metric.ball c r := by
      dsimp only [y]
      rw [Metric.mem_ball, AffineMap.homothety_apply, dist_eq_norm,
        vadd_eq_add, vsub_eq_sub, add_sub_cancel_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos hs]
      have hzdist : dist z c ≤ 1 := by
        simpa only [Metric.mem_closedBall] using hz
      have hzNorm : ‖z - c‖ ≤ 1 := by
        simpa only [dist_eq_norm] using hzdist
      dsimp only [s]
      nlinarith only [hr, hzNorm, norm_nonneg (z - c)]
    refine ⟨y, hballP hyBall, ?_⟩
    dsimp only [f, y]
    rw [← AffineMap.homothety_mul_apply]
    simp only [inv_mul_cancel₀ hs.ne', AffineMap.homothety_one,
      AffineMap.id_apply]
  have hQouter : HasSmoothJordanOuterApproximation Q := hunit v c hunitQ
  have hback : AffineMap.homothety c s '' Q = P := by
    have hcomp :
        (AffineMap.homothety c s : ℂ → ℂ) ∘ f = id := by
      funext z
      dsimp only [f, Function.comp_apply, id_eq]
      rw [← AffineMap.homothety_mul_apply]
      simp only [mul_inv_cancel₀ hs.ne', AffineMap.homothety_one,
        AffineMap.id_apply]
    calc
      AffineMap.homothety c s '' Q =
          AffineMap.homothety c s '' (f '' P) := by rw [hQimage]
      _ = ((AffineMap.homothety c s : ℂ → ℂ) ∘ f) '' P :=
        Set.image_image _ _ P
      _ = P := by rw [hcomp, Set.image_id]
  change HasSmoothJordanOuterApproximation P
  rw [← hback]
  exact hQouter.homothety c s hs.ne'
