-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:08:26.074829+00:00
-- url     : https://prove2.me/submissions/a2827092-dd1e-4f8b-8676-556504559d08

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega 0 xi = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanionBoundaryValue_smul
      Omega 0 (0 : Polynomial ℂ) xi)
