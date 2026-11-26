-- Prove2me | Theorems.Thm_ConcatPiecewiseGeodesic
-- name    : ConcatPiecewiseGeodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:46.481973+00:00
-- url     : https://prove2.me/theorems/33809631-d7e5-4843-9e6d-16a28885862c
-- title:
--   Concat Piecewise Geodesic: Concat Piecewise Geodesic
-- statement:
--   The concatenation of a piecewise geodesic with `k₁` edges and a piecewise geodesic with `k₂`
--   edges is piecewise geodesic with `k₁ + k₂` edges (needed, with the counted form, so that
--   `C1SmallBall`'s Morrey bound `2k` can be applied to a concatenated curve).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConcatPiecewiseGeodesic.lean#L10-L97
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConcatPiecewiseGeodesic.lean#L10-L97

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_ConcatPiecewiseGeodesic
set_option autoImplicit false
open Set

theorem ConcatPiecewiseGeodesic {E : Type*} [MetricSpace E] (γ₁ γ₂ : Curve E)
    (h : γ₁.toFun γ₁.len = γ₂.toFun 0) (k₁ k₂ : ℕ)
    (h₁ : IsPiecewiseGeodesicWith γ₁ k₁) (h₂ : IsPiecewiseGeodesicWith γ₂ k₂) :
    IsPiecewiseGeodesicWith (curveConcat γ₁ γ₂ h) (k₁ + k₂) := by sorry
