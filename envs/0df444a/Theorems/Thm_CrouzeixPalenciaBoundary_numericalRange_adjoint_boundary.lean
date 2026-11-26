-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_numericalRange_adjoint_boundary
-- name    : CrouzeixPalenciaBoundary.numericalRange_adjoint_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:18:09.885184+00:00
-- url     : https://prove2.me/theorems/127b0282-c024-4232-b8b8-d26154066acd
-- title:
--   Crouzeix Palencia Boundary: numerical Range adjoint boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the numerical Range adjoint boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L60-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L60-L63

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem CrouzeixPalenciaBoundary.numericalRange_adjoint_boundary (A : E →L[ℂ] E) :
    numericalRange (ContinuousLinearMap.adjoint A) =
      (starRingEnd ℂ) '' numericalRange A := by sorry
