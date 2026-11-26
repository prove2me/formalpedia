-- Prove2me | Theorems.Thm_ContinuousLinearMap_intervalIntegral_smul_add_adjoint
-- name    : ContinuousLinearMap.intervalIntegral_smul_add_adjoint
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:43.393996+00:00
-- url     : https://prove2.me/theorems/191219f9-e248-52e3-aec3-b700b30181ac
-- title:
--   Continuous Linear Map: interval Integral smul add adjoint
-- statement:
--   Complex-weighted symmetrization of an operator-valued interval integral.
--   The conjugate weight before taking adjoint becomes the original weight, so
--   the two terms combine into the symmetric kernel `K t + (K t)†`.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L72-L106
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L72-L106

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

theorem ContinuousLinearMap.intervalIntegral_smul_add_adjoint (K : ℝ → E →L[ℂ] E) (f : ℝ → ℂ)
    {a b : ℝ} {ν : Measure ℝ}
    (hfK : IntervalIntegrable (fun t => f t • K t) ν a b)
    (hstarfK : IntervalIntegrable (fun t => star (f t) • K t) ν a b) :
    (∫ t in a..b, f t • K t ∂ν) +
        ContinuousLinearMap.adjoint (∫ t in a..b, star (f t) • K t ∂ν) =
      ∫ t in a..b,
        f t • (K t + ContinuousLinearMap.adjoint (K t)) ∂ν := by sorry
