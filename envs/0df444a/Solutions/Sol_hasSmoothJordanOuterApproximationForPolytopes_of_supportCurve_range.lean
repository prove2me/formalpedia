-- Prove2me | solution 1 for hasSmoothJordanOuterApproximationForPolytopes_of_supportCurve_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:50:59.965554+00:00
-- url     : https://prove2.me/submissions/45d63496-806e-4f14-8e75-8de120876f7d

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange
import Definitions.Def_Operator_Crouzeix_SmoothSupportEnvelopeTight
import Definitions.Def_Operator_Crouzeix_SmoothSupportDomain
import Theorems.Thm_polytopeRoundedSupportDomainOfRange_carrier
import Theorems.Thm_Finset_nonempty_of_interior_convexHull_nonempty
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
import Theorems.Thm_exists_tight_polytopeRoundedSupportEnvelope
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


attribute [local simp] polytopeRoundedSupportDomainOfRange_carrier

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff InnerProductSpace
theorem _root_.solution
    (hrange : ∀ {u : Finset ℂ} (_hu : u.Nonempty) {delta rho : ℝ},
      0 < delta → 0 < rho →
      Set.range (polytopeRoundedSupportCurve u delta rho) =
        frontier (smoothSupportOpenEnvelope
          (polytopeRoundedSupport u delta rho))) :
    HasSmoothJordanOuterApproximationForPolytopes := by
  intro u hinterior
  have hu : u.Nonempty :=
    Finset.nonempty_of_interior_convexHull_nonempty hinterior
  intro epsilon hepsilon
  obtain ⟨delta, rho, hdelta, hrho, hin, hout⟩ :=
    exists_tight_polytopeRoundedSupportEnvelope hu hepsilon
  let Omega : SmoothJordanDomain :=
    polytopeRoundedSupportDomainOfRange hu hdelta hrho
      (hrange hu hdelta hrho)
  refine ⟨Omega, ?_, ?_⟩
  · simpa only [Omega, polytopeRoundedSupportDomainOfRange_carrier] using hin
  · simpa only [Omega, polytopeRoundedSupportDomainOfRange_carrier] using hout
