-- Prove2me | solution 1 for polytopeDirectionalValue_le_softSupport_of_mem_convexHull
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:34.595689+00:00
-- url     : https://prove2.me/submissions/d2525445-ebc4-4e5c-918c-007f70d2b61d

import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Definitions.Def_Operator_Crouzeix_PolytopeSoftSupport
import Theorems.Thm_polytopeDirectionalValue_le_softSupport
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



set_option autoImplicit false
open Complex Set
open scoped ContDiff
theorem _root_.solution
    {u : Finset ℂ} {z : ℂ} (hz : z ∈ convexHull ℝ (u : Set ℂ))
    {delta : ℝ} (hdelta : 0 < delta) (theta : ℝ) :
    polytopeDirectionalValue z theta ≤
      polytopeSoftSupport u delta theta := by
  let f : ℂ →ₗ[ℝ] ℝ :=
    Real.cos theta • Complex.reCLM.toLinearMap +
      Real.sin theta • Complex.imCLM.toLinearMap
  have hf (w : ℂ) : f w = polytopeDirectionalValue w theta := by
    dsimp only [f, polytopeDirectionalValue]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change Real.cos theta * Complex.reCLM w +
      Real.sin theta * Complex.imCLM w =
        w.re * Real.cos theta + w.im * Real.sin theta
    rw [Complex.reCLM_apply, Complex.imCLM_apply]
    ring
  have hvertices : (u : Set ℂ) ⊆
      {w | f w ≤ polytopeSoftSupport u delta theta} := by
    intro w hw
    change f w ≤ polytopeSoftSupport u delta theta
    rw [hf]
    exact polytopeDirectionalValue_le_softSupport hw hdelta theta
  have hhalf : Convex ℝ {w | f w ≤ polytopeSoftSupport u delta theta} :=
    convex_halfSpace_le f.isLinear _
  rw [← hf z]
  exact convexHull_min hvertices hhalf hz
