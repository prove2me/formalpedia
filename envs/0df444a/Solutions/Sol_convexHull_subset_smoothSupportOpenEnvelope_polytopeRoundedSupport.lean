-- Prove2me | solution 1 for convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:13.162785+00:00
-- url     : https://prove2.me/submissions/0be99c29-7adf-4ec6-85bd-a379ecf60840

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelope
import Theorems.Thm_smoothSupportDirectionalLinearMap_apply
import Theorems.Thm_polytopeDirectionalValue_le_add_dist
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
import Theorems.Thm_polytopeDirectionalValue_le_softSupport_of_mem_convexHull
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
open scoped ComplexConjugate
theorem _root_.solution
    {u : Finset ℂ} {delta rho : ℝ} (hdelta : 0 < delta)
    (hrho : 0 < rho) :
    convexHull ℝ (u : Set ℂ) ⊆
      smoothSupportOpenEnvelope (polytopeRoundedSupport u delta rho) := by
  intro z hz
  rw [smoothSupportOpenEnvelope, mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrho))
  intro w hw
  change ∀ theta, polytopeDirectionalValue w theta ≤
    polytopeRoundedSupport u delta rho theta
  intro theta
  have hzsupport :=
    polytopeDirectionalValue_le_softSupport_of_mem_convexHull
      hz hdelta theta
  have hdist : dist w z < rho := by
    simpa only [Metric.mem_ball] using hw
  unfold polytopeRoundedSupport
  exact (polytopeDirectionalValue_le_add_dist z w theta).trans
    (by linarith)
