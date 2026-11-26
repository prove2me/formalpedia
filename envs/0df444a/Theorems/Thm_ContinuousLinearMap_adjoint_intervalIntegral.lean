-- Prove2me | Theorems.Thm_ContinuousLinearMap_adjoint_intervalIntegral
-- name    : ContinuousLinearMap.adjoint_intervalIntegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:34:09.801915+00:00
-- url     : https://prove2.me/theorems/06f4ea6e-f48f-4112-9563-bc86e9a71753
-- title:
--   Continuous Linear Map: adjoint interval Integral
-- statement:
--   Adjoint commutes with an operator-valued interval integral whenever the
--   integrand is interval integrable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L49-L54
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L49-L54

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

theorem ContinuousLinearMap.adjoint_intervalIntegral (f : ℝ → E →L[ℂ] F) {a b : ℝ}
    {ν : Measure ℝ} (hf : IntervalIntegrable f ν a b) :
    ContinuousLinearMap.adjoint (∫ x in a..b, f x ∂ν) =
      ∫ x in a..b, ContinuousLinearMap.adjoint (f x) ∂ν := by sorry
