-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_crouzeix_palencia_boundary
-- name    : CrouzeixPalenciaBoundary.crouzeix_palencia_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:18:09.663516+00:00
-- url     : https://prove2.me/theorems/182e4649-5cc8-48c7-b9fa-2ce69215a0e7
-- title:
--   Crouzeix Palencia Boundary: crouzeix palencia boundary
-- statement:
--   Exact unconditional project capstone. This declaration is deliberately
--   part of the manifest boundary so supporting lemmas cannot produce a vacuous
--   green board while the final theorem is absent.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L68-L71
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L68-L71

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem CrouzeixPalenciaBoundary.crouzeix_palencia_boundary (A : E →L[ℂ] E) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by sorry
