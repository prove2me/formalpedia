-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_convex_numericalRange_boundary
-- name    : CrouzeixPalenciaBoundary.convex_numericalRange_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:18:07.22442+00:00
-- url     : https://prove2.me/theorems/010f30cd-1c0f-42d6-813a-a048e4deba6a
-- title:
--   Crouzeix Palencia Boundary: convex numerical Range boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the convex numerical Range boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L33-L35
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L33-L35

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem CrouzeixPalenciaBoundary.convex_numericalRange_boundary (A : E →L[ℂ] E) :
    Convex ℝ (numericalRange A) := by sorry
