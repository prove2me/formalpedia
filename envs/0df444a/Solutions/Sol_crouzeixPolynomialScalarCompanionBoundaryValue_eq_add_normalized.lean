-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_eq_add_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:47.49947+00:00
-- url     : https://prove2.me/submissions/f42d836b-c521-4a19-aaa5-64d0863522c4

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_eval_sub_C_eval_eq_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        crouzeixPolynomialScalarCompanionBoundaryValue Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_sub_C_eval,
    eval_sub_C_eval_eq_zero]
  simp only [star_zero, zero_add]
