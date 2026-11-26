-- Prove2me | solution 1 for hasSmoothJordanOuterApproximation_of_polytope_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:49.783986+00:00
-- url     : https://prove2.me/submissions/75008abf-2211-49ce-a940-b16d00d126ca

import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximationReduction
import Mathlib.Analysis.Normed.Affine.Convex
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
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
open Complex Metric Set
open scoped InnerProductSpace
theorem _root_.solution
    {K : Set ℂ} (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hKconvex : Convex ℝ K)
    (hpoly : HasSmoothJordanOuterApproximationForPolytopes) :
    HasSmoothJordanOuterApproximation K := by
  intro ε hε
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by
    dsimp only [δ]
    linarith
  obtain ⟨u, hKinterior, hpolyTarget⟩ :=
    hKconvex.exists_subset_interior_convexHull_finset_of_isCompact
      hKcompact (Metric.thickening_mem_nhdsSet K hδ)
  let P : Set ℂ := convexHull ℝ (u : Set ℂ)
  have hKP : K ⊆ P := by
    exact hKinterior.trans interior_subset
  have hPinterior : (interior P).Nonempty := by
    exact hKnonempty.mono hKinterior
  obtain ⟨Omega, hPOmega, hOmegaP⟩ := hpoly u hPinterior δ hδ
  refine ⟨Omega, hKP.trans hPOmega, hOmegaP.trans ?_⟩
  have hsum : δ + δ = ε := by
    dsimp only [δ]
    ring
  calc
    Metric.thickening δ P ⊆
        Metric.thickening δ (Metric.thickening δ K) :=
      Metric.thickening_subset_of_subset δ hpolyTarget
    _ = Metric.thickening ε K := by
      rw [thickening_thickening hδ hδ, hsum]
