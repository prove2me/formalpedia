-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_add_C
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:00.962775+00:00
-- url     : https://prove2.me/submissions/b642c699-ea32-42c1-b7eb-f048fe757183

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
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
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (a xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega
        (p + Polynomial.C a) xi z =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
  unfold crouzeixPolynomialScalarCompanionRegularized
  congr 1
  unfold contourIntegral
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Polynomial.eval_add, Polynomial.eval_C, star_add]
  ring
