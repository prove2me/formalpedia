-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:28:09.262653+00:00
-- url     : https://prove2.me/submissions/4f89ccf2-c9a3-44b6-8595-e6f89057f641

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
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
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) {z : ℂ}
    (hz : z ∉ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanion Omega (p + q) z =
      crouzeixPolynomialScalarCompanion Omega p z +
        crouzeixPolynomialScalarCompanion Omega q z := by
  let xi : ℂ := Omega.boundaryParam 0
  rw [crouzeixPolynomialScalarCompanion_eq_regularized_add
      Omega (p + q) xi hz,
    crouzeixPolynomialScalarCompanion_eq_regularized_add Omega p xi hz,
    crouzeixPolynomialScalarCompanion_eq_regularized_add Omega q xi hz,
    crouzeixPolynomialScalarCompanionRegularized_add_of_not_mem_frontier
      Omega p q xi hz]
  simp only [Polynomial.eval_add, star_add]
  ring
