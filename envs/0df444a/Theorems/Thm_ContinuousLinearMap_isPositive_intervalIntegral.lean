-- Prove2me | Theorems.Thm_ContinuousLinearMap_isPositive_intervalIntegral
-- name    : ContinuousLinearMap.isPositive_intervalIntegral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:44:51.08986+00:00
-- url     : https://prove2.me/theorems/3309d622-136c-5ed2-8448-166e27d524d8
-- title:
--   Continuous Linear Map: is Positive interval Integral
-- statement:
--   A positively oriented interval integral of positive operators is
--   positive.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean#L67-L73
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean#L67-L73

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

theorem ContinuousLinearMap.isPositive_intervalIntegral (f : ℝ → E →L[ℂ] E) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hpos : ∀ᵐ x ∂volume.restrict (Set.Ioc a b), IsPositive (f x)) :
    IsPositive (∫ x in a..b, f x) := by sorry
