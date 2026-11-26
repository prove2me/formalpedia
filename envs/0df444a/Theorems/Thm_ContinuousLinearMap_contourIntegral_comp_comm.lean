-- Prove2me | Theorems.Thm_ContinuousLinearMap_contourIntegral_comp_comm
-- name    : ContinuousLinearMap.contourIntegral_comp_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:45.716631+00:00
-- url     : https://prove2.me/theorems/a3287bac-5daa-4f7c-b326-35e67d894983
-- title:
--   Continuous Linear Map: contour Integral comp comm
-- statement:
--   Continuous complex-linear maps commute with contour integrals.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L99-L104
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L99-L104

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem ContinuousLinearMap.contourIntegral_comp_comm [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℂ] G)
    {f : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => L (f z)) γ = L (contourIntegral f γ) := by sorry
