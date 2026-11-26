-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:08.35584+00:00
-- url     : https://prove2.me/submissions/bfbb46b5-a0d5-4e6e-a2d5-e66903de18df

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega 0 xi z = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanionRegularized_smul
      Omega 0 (0 : Polynomial ℂ) xi z)
