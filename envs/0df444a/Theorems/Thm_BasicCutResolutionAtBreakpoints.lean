-- Prove2me | Theorems.Thm_BasicCutResolutionAtBreakpoints
-- name    : BasicCutResolutionAtBreakpoints
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:15:02.800583+00:00
-- url     : https://prove2.me/theorems/d4756988-6007-5982-a251-b9638f74546e
-- title:
--   Basic Cut Resolution At Breakpoints: Basic Cut Resolution At Breakpoints
-- statement:
--   When the two cut points of `BasicCut` are themselves breakpoints `s p, s q` of a given
--   geodesic resolution `(k,s)` of `γ`, the "kept" output `γ'` of the cut admits an explicit geodesic
--   resolution built from the surviving edges of `s` plus the one new closing edge, so its number of
--   small (length `< δ`) edges is at most one more than the number of small edges of `s` lying outside
--   the excised arc between indices `p` and `q`. Phrased without natural-number subtraction: the small
--   edge counts of the excised arc and of `γ'` together are at most one more than the small edge count
--   of the whole resolution `s`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutResolutionAtBreakpoints.lean#L22-L278
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutResolutionAtBreakpoints.lean#L22-L278

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_SubResolutionShortEdgeCount
import Definitions.Def_Tablet_ConcatResolutionShortEdgeCount
import Definitions.Def_Tablet_BasicCutResolutionAtBreakpoints
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_ConcatResolutionShortEdgeCount
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_RestrictPiecewiseGeodesic
import Theorems.Thm_SubResolutionShortEdgeCount

set_option autoImplicit false
open Set

theorem BasicCutResolutionAtBreakpoints {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s) (p q : ℕ) (hp : p ≤ k) (hq : q ≤ k)
    (hne : s p ≠ s q) (δ : ℝ)
    (ht0 : 0 ≤ s p) (htlen : s p ≤ γ.len) (ht'0 : 0 ≤ s q) (ht'len : s q ≤ γ.len) :
    smallPieceCount (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).1 δ
      + ((Finset.Icc 1 k).filter (fun j =>
          (if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j) ∧ s j - s (j - 1) < δ)).card
      ≤ ((Finset.Icc 1 k).filter (fun j => s j - s (j - 1) < δ)).card + 1 := by sorry
