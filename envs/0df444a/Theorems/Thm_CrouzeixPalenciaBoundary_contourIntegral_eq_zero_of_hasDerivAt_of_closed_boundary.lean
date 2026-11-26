-- Prove2me | Theorems.Thm_CrouzeixPalenciaBoundary_contourIntegral_eq_zero_of_hasDerivAt_of_closed_boundary
-- name    : CrouzeixPalenciaBoundary.contourIntegral_eq_zero_of_hasDerivAt_of_closed_boundary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:18:15.745818+00:00
-- url     : https://prove2.me/theorems/4715f2bb-c7a6-48f0-ab61-99e7db373ef0
-- title:
--   Crouzeix Palencia Boundary: contour Integral eq zero of has Deriv At of closed boundary
-- statement:
--   The Crouzeix Palencia Boundary construction uses the contour Integral eq zero of has Deriv At of closed boundary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L114-L120
-- source:
--   https://github.com/savarin/lean-operator-theory/blob/6f90bb7e6b056b54f56005e0416d77d6d7c2a478/Operator/BoundaryCheck.lean#L114-L120

import Definitions.Def_Operator
import Definitions.Def_Operator_BoundaryCheck
set_option autoImplicit false
open Complex ContinuousLinearMap Metric Polynomial Set
open scoped ENNReal InnerProductSpace Interval Real
open CrouzeixPalenciaBoundary
universe u
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem CrouzeixPalenciaBoundary.contourIntegral_eq_zero_of_hasDerivAt_of_closed_boundary
    {f Fp : ℂ → F} {γ : ℝ → ℂ}
    (hγ : ∀ t ∈ Icc (0 : ℝ) (2 * π), DifferentiableAt ℝ γ t)
    (hF : ∀ t ∈ Icc (0 : ℝ) (2 * π), HasDerivAt Fp (f (γ t)) (γ t))
    (hint : ContourIntegrable f γ) (hclosed : γ (2 * π) = γ 0) :
    contourIntegral f γ = 0 := by sorry
