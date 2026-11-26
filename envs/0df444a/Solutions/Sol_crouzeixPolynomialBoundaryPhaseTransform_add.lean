-- Prove2me | solution 1 for crouzeixPolynomialBoundaryPhaseTransform_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:22:18.102797+00:00
-- url     : https://prove2.me/submissions/c9e04768-4eab-4ac9-9bc0-f249eac74c69

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
import Theorems.Thm_contourIntegral_add
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
    (Omega : SmoothJordanDomain) (xi : ℂ) (p q : Polynomial ℂ) :
    crouzeixPolynomialBoundaryPhaseTransform Omega xi (p + q) =
      crouzeixPolynomialBoundaryPhaseTransform Omega xi p +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi q := by
  unfold crouzeixPolynomialBoundaryPhaseTransform
  have hfun :
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma (p + q)) *
          (sigma - xi)⁻¹) =
        fun sigma ↦
          star (sigma - xi) * star (Polynomial.eval sigma p) *
              (sigma - xi)⁻¹ +
            star (sigma - xi) * star (Polynomial.eval sigma q) *
              (sigma - xi)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_add, star_add]
    ring
  rw [hfun, contourIntegral_add
    (contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
      Omega xi p)
    (contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
      Omega xi q)]
  ring
