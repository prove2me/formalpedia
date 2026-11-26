-- Prove2me | solution 1 for crouzeixPolynomialBoundaryPhaseTransform_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:46.655963+00:00
-- url     : https://prove2.me/submissions/1c33585d-0475-412d-817c-6c824bcd2f31

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi 0 = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialBoundaryPhaseTransform_smul
      Omega xi 0 (0 : Polynomial ℂ))
