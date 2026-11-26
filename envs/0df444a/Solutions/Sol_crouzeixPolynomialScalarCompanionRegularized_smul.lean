-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:06.694696+00:00
-- url     : https://prove2.me/submissions/6db0c014-607c-4289-8ae6-d1a65d4f152f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_contourIntegral_smul
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
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ) (xi z : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega (a • p) xi z =
      star a *
        crouzeixPolynomialScalarCompanionRegularized Omega p xi z := by
  unfold crouzeixPolynomialScalarCompanionRegularized
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma (a • p)) -
            star (Polynomial.eval xi (a • p))) *
          (sigma - z)⁻¹) =
        fun sigma ↦ star a •
          ((star (Polynomial.eval sigma p) -
              star (Polynomial.eval xi p)) * (sigma - z)⁻¹) := by
    funext sigma
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, contourIntegral_smul]
  simp only [smul_eq_mul]
  ring
