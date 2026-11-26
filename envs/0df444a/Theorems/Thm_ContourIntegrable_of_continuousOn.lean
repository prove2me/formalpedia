-- Prove2me | Theorems.Thm_ContourIntegrable_of_continuousOn
-- name    : ContourIntegrable.of_continuousOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:29:47.540648+00:00
-- url     : https://prove2.me/theorems/fdc169eb-c389-5dff-9b08-dbd9b9aca72f
-- title:
--   Contour Integrable: of continuous On
-- statement:
--   A function continuous on the trace of a curve with continuous derivative is contour
--   integrable.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L59-L64
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/ContourIntegral.lean#L59-L64

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral
set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem ContourIntegrable.of_continuousOn {f : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ContinuousOn γ (Icc 0 (2 * π))) (hγ' : ContinuousOn (deriv γ) (Icc 0 (2 * π)))
    (hf : ContinuousOn f (γ '' Icc 0 (2 * π))) : ContourIntegrable f γ := by sorry
