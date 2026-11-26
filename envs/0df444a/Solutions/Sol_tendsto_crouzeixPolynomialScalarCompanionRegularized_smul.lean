-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:42.460734+00:00
-- url     : https://prove2.me/submissions/a8d0d1ed-4997-45b6-b614-84bbb4f35e7d

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_smul

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi : ℂ)
    {l : Filter ℂ}
    (h : Tendsto (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      l
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi))) :
    Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi)
      l
      (nhds (crouzeixPolynomialScalarCompanionRegularized
        Omega (a • p) xi xi)) := by
  have hfun :
      crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi =
        fun z ↦ star a *
          crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
    funext z
    exact crouzeixPolynomialScalarCompanionRegularized_smul
      Omega a p xi z
  rw [hfun]
  exact tendsto_const_nhds.mul h
