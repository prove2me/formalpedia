-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_add_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:55.667492+00:00
-- url     : https://prove2.me/submissions/25be32b3-1090-4a15-b17b-e41663e1161f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundary
import Mathlib.Algebra.Polynomial.FieldDivision
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
import Theorems.Thm_contourIntegral_add
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange


attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega (p + q) xi xi =
      crouzeixPolynomialScalarCompanionRegularized Omega p xi xi +
        crouzeixPolynomialScalarCompanionRegularized Omega q xi xi := by
  have hp :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega p xi
  have hq :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega q xi
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma (p + q)) -
            star (Polynomial.eval xi (p + q))) * (sigma - xi)⁻¹) =
        fun sigma ↦
          (star (Polynomial.eval sigma p) - star (Polynomial.eval xi p)) *
              (sigma - xi)⁻¹ +
            (star (Polynomial.eval sigma q) - star (Polynomial.eval xi q)) *
              (sigma - xi)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_add, star_add]
    ring
  unfold crouzeixPolynomialScalarCompanionRegularized
  rw [hfun, contourIntegral_add hp hq]
  ring
