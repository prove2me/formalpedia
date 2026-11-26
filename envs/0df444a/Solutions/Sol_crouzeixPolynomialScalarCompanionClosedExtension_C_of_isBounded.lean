-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:44.560472+00:00
-- url     : https://prove2.me/submissions/0ad56bed-080f-4304-98b3-8a837e3bb64c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_add_C
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_add_C
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
    (Omega : SmoothJordanDomain) (a : ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (Polynomial.C a) z = star a := by
  rw [closure_eq_self_union_frontier] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq Omega _ hz]
    have hzfrontier : z ∉ frontier Omega.carrier := by
      intro hfrontier
      have hempty : z ∈ (∅ : Set ℂ) := by
        rw [← Omega.isOpen_carrier.inter_frontier_eq]
        exact ⟨hz, hfrontier⟩
      exact hempty
    have hshift := crouzeixPolynomialScalarCompanion_add_C
      Omega 0 a hzfrontier
    simpa only [zero_add, crouzeixPolynomialScalarCompanion_zero,
      hkernel z hz, mul_one, add_zero] using hshift
  · rw [
      crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
        Omega (Polynomial.C a) hbounded hkernel hz]
    have hshift :=
      crouzeixPolynomialScalarCompanionBoundaryValue_add_C Omega 0 a z
    simpa only [zero_add,
      crouzeixPolynomialScalarCompanionBoundaryValue_zero, add_zero] using
      hshift
