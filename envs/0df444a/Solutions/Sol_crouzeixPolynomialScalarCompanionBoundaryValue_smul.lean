-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:06:40.019601+00:00
-- url     : https://prove2.me/submissions/e41d1e4e-508b-4218-8b1b-2e3d0b3575eb

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_smul

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega (a • p) xi =
      star a *
        crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_smul]
  have heval : star (Polynomial.eval xi (a • p)) =
      star a * star (Polynomial.eval xi p) := by
    rw [Polynomial.eval_smul]
    change (starRingEnd ℂ) (a * Polynomial.eval xi p) =
      (starRingEnd ℂ) a * (starRingEnd ℂ) (Polynomial.eval xi p)
    exact map_mul (starRingEnd ℂ) a (Polynomial.eval xi p)
  rw [heval]
  ring
