-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator_boundary
-- name    : CrouzeixPalenciaBoundary.exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:18:43.780363+00:00
-- url     : https://prove2.me/theorems/db8adb46-a0ad-5d1c-9952-b82335eeb06e
-- title:
--   Crouzeix Palencia Boundary: exists smooth Jordan Domain norm bound crouzeix Polynomial Auxiliary Operator boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the exists smooth Jordan Domain norm bound crouzeix Polynomial Auxiliary Operator boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L154-L160
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L154-L160

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem CrouzeixPalenciaBoundary.exists_smoothJordanDomain_norm_bound_crouzeixPolynomialAuxiliaryOperator_boundary
    [CompleteSpace E] (A : E →L[ℂ] E) (p : Polynomial ℂ) :
    ∃ (Omega : SmoothJordanDomain) (C : ℝ),
      closure (numericalRange A) ⊆ Omega.carrier ∧
        ‖crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ * (2 * Real.pi * C) := by sorry
