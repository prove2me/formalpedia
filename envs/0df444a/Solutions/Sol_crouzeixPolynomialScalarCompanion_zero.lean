-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:39:20.941845+00:00
-- url     : https://prove2.me/submissions/e0708fb0-fb48-409f-ad1f-60fdb71e6cd3

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_crouzeixPolynomialScalarCompanion_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (z : ℂ) :
    crouzeixPolynomialScalarCompanion Omega 0 z = 0 := by
  simpa only [zero_smul, star_zero, zero_mul] using
    (crouzeixPolynomialScalarCompanion_smul Omega 0 (0 : Polynomial ℂ) z)
