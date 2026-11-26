-- Prove2me | solution 1 for contourIntegrable_crouzeixPolynomialBoundaryPhaseTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:03.670678+00:00
-- url     : https://prove2.me/submissions/9165e712-4a66-40c2-8feb-f018e4e5a8ad

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
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
    (Omega : SmoothJordanDomain) (xi : ℂ) (q : Polynomial ℂ) :
    ContourIntegrable
      (fun sigma ↦
        star (sigma - xi) * star (Polynomial.eval sigma q) *
          (sigma - xi)⁻¹)
      Omega.boundaryParam := by
  have h :=
    contourIntegrable_crouzeixPolynomialScalarCompanionRegularized_self
      Omega ((Polynomial.X - Polynomial.C xi) * q) xi
  have hfun :
      (fun sigma ↦
        (star (Polynomial.eval sigma
              ((Polynomial.X - Polynomial.C xi) * q)) -
            star (Polynomial.eval xi
              ((Polynomial.X - Polynomial.C xi) * q))) *
          (sigma - xi)⁻¹) =
        fun sigma ↦
          star (sigma - xi) * star (Polynomial.eval sigma q) *
            (sigma - xi)⁻¹ := by
    funext sigma
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self, zero_mul, star_zero, sub_zero, star_mul]
    ring
  rw [hfun] at h
  exact h
