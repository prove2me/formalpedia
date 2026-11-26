-- Prove2me | Theorems.Thm_ContinuousLinearMap_adjoint_integral
-- name    : ContinuousLinearMap.adjoint_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:36:44.060169+00:00
-- url     : https://prove2.me/theorems/51bf448d-afc3-4e2b-b3d6-d330e3fbd6ee
-- title:
--   Continuous Linear Map: adjoint integral
-- statement:
--   Adjoint commutes with an integrable operator-valued Bochner integral.
--   The proof uses adjoint as a continuous conjugate-linear map and the fact that
--   complex conjugation fixes real scalars.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L39-L45
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L39-L45

import Definitions.Def_Operator_Crouzeix_ContourIntegral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Definitions.Def_Operator_Crouzeix_AdjointIntegral
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace Interval
universe u v w
open ContinuousLinearMap
variable {X : Type u} [MeasurableSpace X] {μ : Measure X}
variable {E : Type v} {F : Type w}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem ContinuousLinearMap.adjoint_integral (f : X → E →L[ℂ] F) (hf : Integrable f μ) :
    ContinuousLinearMap.adjoint (∫ x, f x ∂μ) =
      ∫ x, ContinuousLinearMap.adjoint (f x) ∂μ := by sorry
