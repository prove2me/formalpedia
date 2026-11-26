-- Prove2me | Theorems.Thm_ContinuousLinearMap_adjoint_contourIntegral
-- name    : ContinuousLinearMap.adjoint_contourIntegral
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T13:30:17.800361+00:00
-- url     : https://prove2.me/theorems/c0376383-0108-43cf-9d0e-aace2a1256bd
-- title:
--   Continuous Linear Map: adjoint contour Integral
-- statement:
--   Moving adjoint through a contour integral conjugates the tangent scalar
--   and takes the pointwise adjoint of the operator-valued integrand.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L58-L67
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/Crouzeix/AdjointIntegral.lean#L58-L67

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

theorem ContinuousLinearMap.adjoint_contourIntegral (f : ℂ → E →L[ℂ] F) (γ : ℝ → ℂ)
    (hf : ContourIntegrable f γ) :
    ContinuousLinearMap.adjoint (contourIntegral f γ) =
      ∫ t in (0 : ℝ)..(2 * Real.pi),
        star (deriv γ t) • ContinuousLinearMap.adjoint (f (γ t)) := by sorry
