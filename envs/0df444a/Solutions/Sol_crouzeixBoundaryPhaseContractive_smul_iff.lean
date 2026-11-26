-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_smul_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:38.704822+00:00
-- url     : https://prove2.me/submissions/6a0e9410-5b92-4e70-847a-59c5219ce7f2

import Definitions.Def_Operator_Crouzeix_ScalarCompanionAssembly
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Theorems.Thm_crouzeixBoundaryPhaseContractive_smul
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
open Complex Filter Set
open scoped InnerProductSpace Interval Real
universe u
theorem _root_.solution
    (Omega : SmoothJordanDomain) {a : ℂ} (ha : a ≠ 0)
    (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive Omega (a • p) ↔
      CrouzeixBoundaryPhaseContractive Omega p := by
  constructor
  · intro h
    have hscaled := crouzeixBoundaryPhaseContractive_smul
      Omega a⁻¹ (a • p) h
    simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hscaled
  · exact crouzeixBoundaryPhaseContractive_smul Omega a p
