-- Prove2me | Theorems.Thm_ContinuousLinearMap_intervalIntegral_mono_ae
-- name    : ContinuousLinearMap.intervalIntegral_mono_ae
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:30:32.489796+00:00
-- url     : https://prove2.me/theorems/e8381cca-838e-5a98-b02a-9fbf66365a61
-- title:
--   Continuous Linear Map: interval Integral mono ae
-- statement:
--   Positively oriented interval integration is monotone for the Loewner
--   order on continuous linear maps.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean#L85-L93
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/PositiveIntegral.lean#L85-L93

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

theorem ContinuousLinearMap.intervalIntegral_mono_ae (f g : ℝ → E →L[ℂ] E) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by sorry
