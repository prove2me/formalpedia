-- Prove2me | solution 1 for polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:28:23.545013+00:00
-- url     : https://prove2.me/submissions/6e65bfb2-40be-43a2-8380-355afd03e34f

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_strictMonoOn_smoothSupportCurve_projection_left
import Theorems.Thm_strictAntiOn_smoothSupportCurve_projection_right
import Theorems.Thm_exists_sub_int_mul_two_pi_mem_Ico
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
import Theorems.Thm_periodic_smoothSupportCurve
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_self
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
open scoped ContDiff
theorem _root_.solution
    {h : ℝ → ℝ} (hsmooth : ContDiff ℝ ∞ h)
    (hperiodic : Function.Periodic h (2 * Real.pi))
    (hcurv : ∀ x, 0 < smoothSupportCurvatureRadius h x)
    (theta phi : ℝ) :
    polytopeDirectionalValue (smoothSupportCurve h phi) theta = h theta ↔
      ∃ k : ℤ, phi = theta + (k : ℝ) * (2 * Real.pi) := by
  constructor
  · intro heq
    obtain ⟨k, hk⟩ := exists_sub_int_mul_two_pi_mem_Ico theta phi
    let psi : ℝ := phi - (k : ℝ) * (2 * Real.pi)
    have hcurvePeriod := periodic_smoothSupportCurve hperiodic
    have hcurveEq : smoothSupportCurve h psi = smoothSupportCurve h phi := by
      exact hcurvePeriod.sub_int_mul_eq k
    have heqPsi :
        polytopeDirectionalValue (smoothSupportCurve h psi) theta = h theta := by
      rw [hcurveEq]
      exact heq
    by_cases hpsi : psi = theta
    · refine ⟨k, ?_⟩
      dsimp [psi] at hpsi
      linarith
    · have hself := polytopeDirectionalValue_smoothSupportCurve_self h theta
      rcases lt_or_gt_of_ne hpsi with hlt | hgt
      · have hstrict := strictMonoOn_smoothSupportCurve_projection_left
          hsmooth hcurv theta
          (show psi ∈ Icc (theta - Real.pi) theta from ⟨hk.1, hlt.le⟩)
          (show theta ∈ Icc (theta - Real.pi) theta from
            ⟨by linarith [Real.pi_pos], le_rfl⟩) hlt
        change polytopeDirectionalValue (smoothSupportCurve h psi) theta <
          polytopeDirectionalValue (smoothSupportCurve h theta) theta at hstrict
        rw [hself, heqPsi] at hstrict
        exact (lt_irrefl _ hstrict).elim
      · have hstrict := strictAntiOn_smoothSupportCurve_projection_right
          hsmooth hcurv theta
          (show theta ∈ Icc theta (theta + Real.pi) from
            ⟨le_rfl, by linarith [Real.pi_pos]⟩)
          (show psi ∈ Icc theta (theta + Real.pi) from
            ⟨hgt.le, hk.2.le⟩) hgt
        change polytopeDirectionalValue (smoothSupportCurve h psi) theta <
          polytopeDirectionalValue (smoothSupportCurve h theta) theta at hstrict
        rw [hself, heqPsi] at hstrict
        exact (lt_irrefl _ hstrict).elim
  · rintro ⟨k, rfl⟩
    have hcurvePeriod := periodic_smoothSupportCurve hperiodic
    rw [(hcurvePeriod.int_mul k) theta]
    exact polytopeDirectionalValue_smoothSupportCurve_self h theta
