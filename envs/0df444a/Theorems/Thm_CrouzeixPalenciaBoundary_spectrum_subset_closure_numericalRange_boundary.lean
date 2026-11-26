-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_spectrum_subset_closure_numericalRange_boundary
-- name    : CrouzeixPalenciaBoundary.spectrum_subset_closure_numericalRange_boundary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:17:15.682365+00:00
-- url     : https://prove2.me/theorems/a67328a5-7252-5ca1-adf9-bf2ac09ed968
-- title:
--   Crouzeix Palencia Boundary: spectrum subset closure numerical Range boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the spectrum subset closure numerical Range boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L56-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L56-L58

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem CrouzeixPalenciaBoundary.spectrum_subset_closure_numericalRange_boundary (A : E →L[ℂ] E) :
    spectrum ℂ (A : E →L[ℂ] E) ⊆ closure (numericalRange A) := by sorry
