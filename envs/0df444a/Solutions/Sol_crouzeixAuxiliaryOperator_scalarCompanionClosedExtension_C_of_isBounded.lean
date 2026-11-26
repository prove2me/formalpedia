-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:14.690806+00:00
-- url     : https://prove2.me/submissions/447de164-d7fb-402c-9bf9-192f9afd182e

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a)) =
      crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by
  unfold crouzeixPolynomialAuxiliaryOperator crouzeixAuxiliaryOperator
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t ht
  have hfrontier : Omega.boundaryParam t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  change deriv Omega.boundaryParam t •
      (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a) (Omega.boundaryParam t) •
        resolvent A (Omega.boundaryParam t)) =
    deriv Omega.boundaryParam t •
      (star (Polynomial.eval (Omega.boundaryParam t) (Polynomial.C a)) •
        resolvent A (Omega.boundaryParam t))
  rw [
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
      Omega a hbounded hkernel (frontier_subset_closure hfrontier)]
  simp only [Polynomial.eval_C]
