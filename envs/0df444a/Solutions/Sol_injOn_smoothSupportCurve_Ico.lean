-- Prove2me | solution 1 for injOn_smoothSupportCurve_Ico
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:15.917846+00:00
-- url     : https://prove2.me/submissions/b01dc715-82e6-4be8-90ce-732771fbdfaa

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Theorems.Thm_polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
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
    (a : ℝ) :
    Set.InjOn (smoothSupportCurve h) (Ico a (a + 2 * Real.pi)) := by
  intro x hx y hy hxy
  simp only [mem_Ico] at hx hy
  have heqProjection :
      polytopeDirectionalValue (smoothSupportCurve h y) x = h x := by
    rw [← hxy]
    exact polytopeDirectionalValue_smoothSupportCurve_self h x
  obtain ⟨k, hyk⟩ :=
    (polytopeDirectionalValue_smoothSupportCurve_eq_self_iff
      hsmooth hperiodic hcurv x y).mp heqProjection
  have hklt : (k : ℝ) < 1 := by
    rw [hyk] at hy
    nlinarith only [hy.2, hx.1, Real.pi_pos]
  have hkgt : (-1 : ℝ) < (k : ℝ) := by
    rw [hyk] at hy
    nlinarith only [hy.1, hx.2, Real.pi_pos]
  have hkltInt : k < 1 := by exact_mod_cast hklt
  have hkgtInt : (-1 : ℤ) < k := by exact_mod_cast hkgt
  have hk : k = 0 := by omega
  subst k
  simpa using hyk.symm
