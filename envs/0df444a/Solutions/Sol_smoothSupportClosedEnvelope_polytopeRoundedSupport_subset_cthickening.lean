-- Prove2me | solution 1 for smoothSupportClosedEnvelope_polytopeRoundedSupport_subset_cthickening
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:04.127112+00:00
-- url     : https://prove2.me/submissions/88b16e63-044c-42fa-bc05-133f3b2b2d64

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Theorems.Thm_polytopeDirectionalValue_sub_at_arg
import Theorems.Thm_real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_canonicalOrientation_hasMergelyanPolynomialApproximation_iff
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_boundaryParam
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_carrier
import Theorems.Thm_SmoothJordanDomain_reverseOrientation_hasMergelyanPolynomialApproximation_iff
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
import Theorems.Thm_polytopeSoftSupport_le_of_forall_directionalValue_le
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
attribute [local simp] SmoothJordanDomain.canonicalOrientation_carrier
attribute [local simp] SmoothJordanDomain.canonicalOrientation_hasMergelyanPolynomialApproximation_iff
attribute [local simp] SmoothJordanDomain.reverseOrientation_boundaryParam
attribute [local simp] SmoothJordanDomain.reverseOrientation_carrier
attribute [local simp] SmoothJordanDomain.reverseOrientation_hasMergelyanPolynomialApproximation_iff
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
attribute [local simp] smoothSupportDirectionalLinearMap_apply



set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {u : Finset ℂ} (hu : u.Nonempty) {delta rho : ℝ}
    (hdelta : 0 < delta) (hrho : 0 ≤ rho) :
    smoothSupportClosedEnvelope (polytopeRoundedSupport u delta rho) ⊆
      Metric.cthickening
        (delta * Real.log (u.card : ℝ) + rho)
        (convexHull ℝ (u : Set ℂ)) := by
  let P : Set ℂ := convexHull ℝ (u : Set ℂ)
  let R : ℝ := delta * Real.log (u.card : ℝ) + rho
  have hPcompact : IsCompact P := by
    exact u.finite_toSet.isCompact_convexHull ℝ
  have hPnonempty : P.Nonempty := by
    obtain ⟨a, ha⟩ := hu
    exact ⟨a, (subset_convexHull ℝ (u : Set ℂ)) ha⟩
  have hPconvex : Convex ℝ P := convex_convexHull ℝ _
  have hcard : (1 : ℝ) ≤ (u.card : ℝ) := by
    exact_mod_cast hu.card_pos
  have hR : 0 ≤ R := by
    dsimp only [R]
    exact add_nonneg (mul_nonneg hdelta.le (Real.log_nonneg hcard)) hrho
  intro z hz
  obtain ⟨v, hvP, hvmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hPnonempty
      hPcompact.isComplete hPconvex z
  have hprojection : ∀ w ∈ P, ⟪z - v, w - v⟫_ℝ ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hPconvex hvP).mp hvmin
  have hzR : dist z v ≤ R := by
    by_cases hzv : z = v
    · subst z
      simpa only [dist_self] using hR
    · let theta : ℝ := (z - v).arg
      have hdir (w : ℂ) (hw : w ∈ P) :
          polytopeDirectionalValue w theta ≤
            polytopeDirectionalValue v theta := by
        have hinner := hprojection w hw
        rw [real_inner_eq_norm_mul_polytopeDirectionalValue_sub_at_arg]
          at hinner
        apply sub_nonpos.mp
        dsimp only [theta]
        exact nonpos_of_mul_nonpos_right hinner
          (norm_pos_iff.mpr (sub_ne_zero.mpr hzv))
      have hsoft : polytopeSoftSupport u delta theta ≤
          polytopeDirectionalValue v theta +
            delta * Real.log (u.card : ℝ) := by
        apply polytopeSoftSupport_le_of_forall_directionalValue_le
          hu hdelta
        intro w hw
        exact hdir w ((subset_convexHull ℝ (u : Set ℂ)) hw)
      have hzenvelope : polytopeDirectionalValue z theta ≤
          polytopeRoundedSupport u delta rho theta := by
        exact hz theta
      have hnorm : ‖z - v‖ ≤ R := by
        rw [← polytopeDirectionalValue_sub_at_arg hzv]
        unfold polytopeRoundedSupport at hzenvelope
        dsimp only [R]
        linarith
      simpa only [dist_eq_norm] using hnorm
  rw [hPcompact.cthickening_eq_biUnion_closedBall hR]
  exact mem_biUnion hvP hzR
