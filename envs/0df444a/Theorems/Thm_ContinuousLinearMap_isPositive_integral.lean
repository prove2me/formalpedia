-- Prove2me | Theorems.Thm_ContinuousLinearMap_isPositive_integral
-- name    : ContinuousLinearMap.isPositive_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:34:57.151073+00:00
-- url     : https://prove2.me/theorems/f8f0f2c6-ca75-49e9-8820-46da2771b6d1
-- title:
--   Continuous Linear Map: is Positive integral
-- statement:
--   The Bochner integral of an integrable family of positive continuous
--   linear maps is positive when the family is positive almost everywhere.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean#L36-L63
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean#L36-L63

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
universe u v
open ContinuousLinearMap
variable {X : Type u} {E : Type v} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem ContinuousLinearMap.isPositive_integral (f : X → E →L[ℂ] E) (hf : Integrable f μ)
    (hpos : ∀ᵐ x ∂μ, IsPositive (f x)) : IsPositive (∫ x, f x ∂μ) := by sorry
