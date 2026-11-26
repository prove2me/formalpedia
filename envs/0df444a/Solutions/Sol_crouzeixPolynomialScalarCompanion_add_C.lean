-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:12.199506+00:00
-- url     : https://prove2.me/submissions/7fe1a3f1-c82d-474e-a3b4-918997462e53

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_C
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_eq_regularized_add
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a : ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega (p + Polynomial.C a) z =
      star a * crouzeixScalarCauchyKernel Omega z +
        crouzeixPolynomialScalarCompanion Omega p z := by
  let xi : ℂ := Omega.boundaryParam 0
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add
      Omega (p + Polynomial.C a) xi hz,
    crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi hz,
    crouzeixPolynomialScalarCompanionRegularized_add_C]
  simp only [Polynomial.eval_add, Polynomial.eval_C, star_add]
  ring
