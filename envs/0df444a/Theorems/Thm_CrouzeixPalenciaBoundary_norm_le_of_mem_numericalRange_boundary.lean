-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_norm_le_of_mem_numericalRange_boundary
-- name    : CrouzeixPalenciaBoundary.norm_le_of_mem_numericalRange_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:17:08.738074+00:00
-- url     : https://prove2.me/theorems/8d3b3f2e-abc2-54ba-93ba-55ef159f538f
-- title:
--   Crouzeix Palencia Boundary: norm le of mem numerical Range boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the norm le of mem numerical Range boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L29-L31
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L29-L31

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem CrouzeixPalenciaBoundary.norm_le_of_mem_numericalRange_boundary (A : E →L[ℂ] E)
    {z : ℂ} (hz : z ∈ numericalRange A) : ‖z‖ ≤ ‖A‖ := by sorry
