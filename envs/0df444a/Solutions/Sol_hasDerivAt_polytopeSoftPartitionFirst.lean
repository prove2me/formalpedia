-- Prove2me | solution 1 for hasDerivAt_polytopeSoftPartitionFirst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:19.876856+00:00
-- url     : https://prove2.me/submissions/37cf7998-d3e9-41e4-ae45-677ea5158924

import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupportCurvature
import Theorems.Thm_hasDerivAt_polytopeDirectionalValue
import Theorems.Thm_hasDerivAt_polytopeDirectionalVelocity
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


section
open Complex Set
open scoped ContDiff
private theorem hasDerivAt_polytopeSoftWeight
    (z : ℂ) (delta theta : ℝ) :
    HasDerivAt
      (fun x => Real.exp (polytopeDirectionalValue z x / delta))
      (Real.exp (polytopeDirectionalValue z theta / delta) *
        (polytopeDirectionalVelocity z theta / delta)) theta := by
  exact (Real.hasDerivAt_exp _).comp theta
    ((hasDerivAt_polytopeDirectionalValue z theta).div_const delta)
private theorem hasDerivAt_polytopeSoftWeight_mul_velocity
    (z : ℂ) (delta theta : ℝ) :
    HasDerivAt
      (fun x => Real.exp (polytopeDirectionalValue z x / delta) *
        (polytopeDirectionalVelocity z x / delta))
      (Real.exp (polytopeDirectionalValue z theta / delta) *
        ((polytopeDirectionalVelocity z theta / delta) ^ 2 -
          polytopeDirectionalValue z theta / delta)) theta := by
  have h := (hasDerivAt_polytopeSoftWeight z delta theta).mul
    ((hasDerivAt_polytopeDirectionalVelocity z theta).div_const delta)
  have hcoef :
      Real.exp (polytopeDirectionalValue z theta / delta) *
          (polytopeDirectionalVelocity z theta / delta) *
          (polytopeDirectionalVelocity z theta / delta) +
        Real.exp (polytopeDirectionalValue z theta / delta) *
          (-polytopeDirectionalValue z theta / delta) =
      Real.exp (polytopeDirectionalValue z theta / delta) *
        ((polytopeDirectionalVelocity z theta / delta) ^ 2 -
          polytopeDirectionalValue z theta / delta) := by
    ring
  rw [hcoef] at h
  apply h.congr_of_eventuallyEq
    (f₁ := fun x => Real.exp (polytopeDirectionalValue z x / delta) *
      (polytopeDirectionalVelocity z x / delta))
  exact Filter.Eventually.of_forall fun x => by
    simp only [Pi.mul_apply]
end

set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    (u : Finset ℂ) (delta theta : ℝ) :
    HasDerivAt (polytopeSoftPartitionFirst u delta)
      (polytopeSoftPartitionSecond u delta theta) theta := by
  unfold polytopeSoftPartitionFirst polytopeSoftPartitionSecond
  have h := HasDerivAt.sum (u := u) fun z hz =>
    hasDerivAt_polytopeSoftWeight_mul_velocity z delta theta
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun x => by
    rw [Finset.sum_apply]
