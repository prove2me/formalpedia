-- Prove2me | Theorems.Thm_ConcatGeodesicResolution
-- name    : ConcatGeodesicResolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:02:15.275719+00:00
-- url     : https://prove2.me/theorems/fbad9b88-1bef-5038-8acc-178e20f7bbb8
-- title:
--   Concat Geodesic Resolution: Concat Geodesic Resolution
-- statement:
--   **Gluing two geodesic resolutions across a matched endpoint, with the glued resolution named.**
--   If `(K₁,r₁)` resolves `η₁` and `(K₂,r₂)` resolves `η₂` and the endpoints match
--   (`η₁.toFun η₁.len = η₂.toFun 0`), then the concatenation `η₁ * η₂` is resolved into `K₁ + K₂`
--   geodesic edges by the explicitly named breakpoint function `i ↦ r₁ i` for `i ≤ K₁` and
--   `i ↦ η₁.len + r₂ (i - K₁)` for `i > K₁`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConcatGeodesicResolution.lean#L12-L100
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/ConcatGeodesicResolution.lean#L12-L100

import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_ConcatGeodesicResolution
set_option autoImplicit false
open Set

theorem ConcatGeodesicResolution {E : Type*} [MetricSpace E] (η₁ η₂ : Curve E)
    (h : η₁.toFun η₁.len = η₂.toFun 0) (K₁ K₂ : ℕ) (r₁ r₂ : ℕ → ℝ)
    (h₁ : IsGeodesicResolution η₁ K₁ r₁) (h₂ : IsGeodesicResolution η₂ K₂ r₂) :
    IsGeodesicResolution (curveConcat η₁ η₂ h) (K₁ + K₂)
      (fun i => if i ≤ K₁ then r₁ i else η₁.len + r₂ (i - K₁)) := by sorry
