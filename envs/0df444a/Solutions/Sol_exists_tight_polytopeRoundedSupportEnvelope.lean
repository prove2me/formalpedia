-- Prove2me | solution 1 for exists_tight_polytopeRoundedSupportEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:25.878978+00:00
-- url     : https://prove2.me/submissions/3fb779ef-26da-4469-90ac-dc2b37250a34

import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeApproximation
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurve
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
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
import Theorems.Thm_closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
import Theorems.Thm_convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
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
    {u : Finset ℂ} (hu : u.Nonempty) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta rho : ℝ,
      0 < delta ∧ 0 < rho ∧
      convexHull ℝ (u : Set ℂ) ⊆
        smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho) ∧
      closure
          (smoothSupportOpenEnvelope
            (polytopeRoundedSupport u delta rho)) ⊆
        Metric.thickening epsilon (convexHull ℝ (u : Set ℂ)) := by
  let L : ℝ := Real.log (u.card : ℝ)
  let Q : ℝ := max 1 L
  let delta : ℝ := epsilon / (4 * Q)
  let rho : ℝ := epsilon / 4
  have hcard : (1 : ℝ) ≤ (u.card : ℝ) := by
    exact_mod_cast hu.card_pos
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact Real.log_nonneg hcard
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 L)
  have hdelta : 0 < delta := by
    dsimp only [delta]
    exact div_pos hepsilon (mul_pos (by norm_num) hQ)
  have hrho : 0 < rho := by
    dsimp only [rho]
    positivity
  have hLQ : L ≤ Q := by
    dsimp only [Q]
    exact le_max_right 1 L
  have hdeltaQ : delta * Q = epsilon / 4 := by
    dsimp only [delta]
    field_simp [hQ.ne']
  have hdeltaL : delta * L ≤ epsilon / 4 := by
    calc
      delta * L ≤ delta * Q :=
        mul_le_mul_of_nonneg_left hLQ hdelta.le
      _ = epsilon / 4 := hdeltaQ
  have hovershoot : delta * Real.log (u.card : ℝ) + rho < epsilon := by
    change delta * L + rho < epsilon
    dsimp only [rho]
    linarith
  refine ⟨delta, rho, hdelta, hrho,
    convexHull_subset_smoothSupportOpenEnvelope_polytopeRoundedSupport
      hdelta hrho, ?_⟩
  exact
    (closure_smoothSupportOpenEnvelope_polytopeRoundedSupport_subset_cthickening
      hu hdelta hrho).trans
      (Metric.cthickening_subset_thickening'
        hepsilon hovershoot (convexHull ℝ (u : Set ℂ)))
