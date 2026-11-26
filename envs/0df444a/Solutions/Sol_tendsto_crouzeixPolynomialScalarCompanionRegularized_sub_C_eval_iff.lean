-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:46.786203+00:00
-- url     : https://prove2.me/submissions/fe3544ee-2516-4737-a257-148bbf59e748

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_sub_C_eval

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ)
    (l : Filter ℂ) :
    Tendsto
        (crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi)
        l
        (nhds (crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi xi)) ↔
      Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
        l
        (nhds
          (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  have hfun :
      crouzeixPolynomialScalarCompanionRegularized Omega
          (p - Polynomial.C (Polynomial.eval xi p)) xi =
        crouzeixPolynomialScalarCompanionRegularized Omega p xi := by
    funext z
    exact crouzeixPolynomialScalarCompanionRegularized_sub_C_eval
      Omega p xi z
  rw [hfun]
