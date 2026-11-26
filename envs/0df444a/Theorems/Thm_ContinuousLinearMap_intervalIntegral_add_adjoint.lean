-- Prove2me | Theorems.Thm_ContinuousLinearMap_intervalIntegral_add_adjoint
-- name    : ContinuousLinearMap.intervalIntegral_add_adjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:36:45.114772+00:00
-- url     : https://prove2.me/theorems/0273749b-ba25-5334-8060-14022a8618c8
-- title:
--   Continuous Linear Map: interval Integral add adjoint
-- statement:
--   Interval integration commutes with symmetrization of an
--   operator-valued integrand.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerIntegral.lean#L43-L58
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/DoubleLayerIntegral.lean#L43-L58

import Definitions.Def_Operator_Crouzeix_AdjointIntegral
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Definitions.Def_Operator_Crouzeix_DoubleLayerIntegral
set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
open ContinuousLinearMap

theorem ContinuousLinearMap.intervalIntegral_add_adjoint {f : ℝ → E →L[ℂ] E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t + ContinuousLinearMap.adjoint (f t)) =
      (∫ t in a..b, f t) +
        ContinuousLinearMap.adjoint (∫ t in a..b, f t) := by sorry
