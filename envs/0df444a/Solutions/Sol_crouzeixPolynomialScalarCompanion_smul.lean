-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:38:33.220233+00:00
-- url     : https://prove2.me/submissions/e1b33bef-c87f-43d3-a718-c65833a4141e

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    crouzeixPolynomialScalarCompanion Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanion Omega p z := by
  unfold crouzeixPolynomialScalarCompanion
  have hfun :
      (fun sigma ↦ star (Polynomial.eval sigma (a • p)) * (sigma - z)⁻¹) =
        fun sigma ↦ star a •
          (star (Polynomial.eval sigma p) * (sigma - z)⁻¹) := by
    funext sigma
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, contourIntegral_smul]
  simp only [smul_eq_mul]
  ring
