-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:43.795496+00:00
-- url     : https://prove2.me/submissions/e7a055ea-83aa-4958-97d3-714ddaeda8c1

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_add_C
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega
        (p + Polynomial.C a) xi =
      star a + crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_add_C]
  simp only [Polynomial.eval_add, Polynomial.eval_C, star_add]
  ring
