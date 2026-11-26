-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionDeriv_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:13.59612+00:00
-- url     : https://prove2.me/submissions/ce39a574-a4af-4dba-8b4c-d420ec5af2e0

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanion_zero

set_option autoImplicit false
open Complex Filter MeasureTheory Set spectrum
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (z : ℂ) :
    crouzeixPolynomialScalarCompanionDeriv Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionDeriv Omega p z := by
  unfold crouzeixPolynomialScalarCompanionDeriv
  have hfun :
      (fun t ↦ deriv Omega.boundaryParam t *
        star (Polynomial.eval (Omega.boundaryParam t) (a • p)) *
          (Omega.boundaryParam t - z)⁻¹ ^ 2) =
        fun t ↦ star a •
          (deriv Omega.boundaryParam t *
            star (Polynomial.eval (Omega.boundaryParam t) p) *
              (Omega.boundaryParam t - z)⁻¹ ^ 2) := by
    funext t
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, intervalIntegral.integral_smul]
  simp only [smul_eq_mul]
  ring
