-- Prove2me | solution 1 for mem_smoothSupportOpenEnvelope_of_forall_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:39.338229+00:00
-- url     : https://prove2.me/submissions/9f4f4f8d-8957-45f0-9c3c-ef88280a0b98

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
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
import Theorems.Thm_contDiff_polytopeDirectionalValue
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_exists_sub_int_mul_two_pi_mem_Ico
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_periodic_polytopeDirectionalValue
import Theorems.Thm_polytopeDirectionalValue_le_add_dist
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
    {h : ℝ → ℝ} (hcontinuous : Continuous h)
    (hperiodic : Function.Periodic h (2 * Real.pi)) {z : ℂ}
    (hz : ∀ theta, polytopeDirectionalValue z theta < h theta) :
    z ∈ smoothSupportOpenEnvelope h := by
  let gap : ℝ → ℝ := fun theta =>
    h theta - polytopeDirectionalValue z theta
  have hgapContinuous : Continuous gap := by
    exact hcontinuous.sub (contDiff_polytopeDirectionalValue z).continuous
  have hgapPeriodic : Function.Periodic gap (2 * Real.pi) := by
    intro theta
    dsimp only [gap]
    rw [hperiodic theta, periodic_polytopeDirectionalValue z theta]
  obtain ⟨r, hr, hrbound⟩ :
      ∃ r : ℝ, 0 < r ∧
        ∀ theta ∈ Icc (0 : ℝ) (2 * Real.pi), r ≤ gap theta :=
    isCompact_Icc.exists_forall_le' hgapContinuous.continuousOn
      (fun theta _ => by
        dsimp only [gap]
        exact sub_pos.mpr (hz theta))
  have hgapLower (theta : ℝ) : r ≤ gap theta := by
    obtain ⟨k, hk⟩ := exists_sub_int_mul_two_pi_mem_Ico Real.pi theta
    let psi : ℝ := theta - (k : ℝ) * (2 * Real.pi)
    have hpsi : psi ∈ Icc (0 : ℝ) (2 * Real.pi) := by
      dsimp only [psi]
      constructor <;> linarith [hk.1, hk.2]
    have hbound := hrbound psi hpsi
    have hgapEq : gap psi = gap theta := by
      exact hgapPeriodic.sub_int_mul_eq k
    rwa [hgapEq] at hbound
  rw [smoothSupportOpenEnvelope, mem_interior_iff_mem_nhds]
  apply Filter.mem_of_superset
    (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (half_pos hr)))
  intro w hw
  change ∀ theta, polytopeDirectionalValue w theta ≤ h theta
  intro theta
  have hdist : dist w z < r / 2 := by
    simpa only [mem_ball] using hw
  have hdir := polytopeDirectionalValue_le_add_dist z w theta
  have hlower := hgapLower theta
  dsimp only [gap] at hlower
  linarith
