-- Prove2me | solution 1 for crouzeixPolynomialBoundaryPhaseTransform_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:45.893364+00:00
-- url     : https://prove2.me/submissions/39027256-4ec1-4286-b9f8-30a2aa4381de

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_contourIntegral_smul
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (xi a : ℂ) (q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi (a • q) =
      star a * crouzeixPolynomialBoundaryPhaseTransform Omega xi q := by
  unfold crouzeixPolynomialBoundaryPhaseTransform
  have hfun :
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma (a • q)) *
          (sigma - xi)⁻¹) =
        fun sigma ↦ star a •
          (star (sigma - xi) * star (Polynomial.eval sigma q) *
            (sigma - xi)⁻¹) := by
    funext sigma
    simp only [Polynomial.eval_smul, smul_eq_mul, star_mul]
    ring
  rw [hfun, contourIntegral_smul]
  simp only [smul_eq_mul]
  ring
