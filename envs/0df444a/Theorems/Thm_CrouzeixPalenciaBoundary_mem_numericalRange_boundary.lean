-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_mem_numericalRange_boundary
-- name    : CrouzeixPalenciaBoundary.mem_numericalRange_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:17:05.11687+00:00
-- url     : https://prove2.me/theorems/8f74363b-1a37-5cc3-b8ff-621580125de6
-- title:
--   Crouzeix Palencia Boundary: mem numerical Range boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the mem numerical Range boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L25-L27
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L25-L27

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem CrouzeixPalenciaBoundary.mem_numericalRange_boundary (A : E →L[ℂ] E) (z : ℂ) :
    z ∈ numericalRange A ↔ ∃ x : E, ‖x‖ = 1 ∧ ⟪x, A x⟫_ℂ = z := by sorry
