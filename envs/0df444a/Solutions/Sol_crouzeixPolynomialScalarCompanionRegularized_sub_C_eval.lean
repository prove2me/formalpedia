-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:51.933971+00:00
-- url     : https://prove2.me/submissions/446a9555-d53e-4369-a041-05bf998018f3

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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega
        (p - Polynomial.C (Polynomial.eval xi p)) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
  simpa only [sub_eq_add_neg, ← Polynomial.C_neg] using
    (crouzeixPolynomialScalarCompanionRegularized_add_C
      Omega p (-Polynomial.eval xi p) xi z)
