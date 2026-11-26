-- Prove2me | Theorems.Thm_BasicCutDiscardedResolution
-- name    : BasicCutDiscardedResolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:12:43.883009+00:00
-- url     : https://prove2.me/theorems/ac577430-6b1a-4c0b-b9d9-55ebb9a9fc8c
-- title:
--   Basic Cut Discarded Resolution: Basic Cut Discarded Resolution
-- statement:
--   When the two cut points of `BasicCut` are breakpoints `s p, s q` of a given geodesic
--   resolution `(k,s)` of `γ`, the "discarded" output `g` of the cut admits an explicit geodesic
--   resolution built from the excised edges of `s` plus the one new closing edge, so its number of
--   pieces is exactly one more than the number of edges of `s` lying in the excised arc between
--   indices `p` and `q` (the same `inArc` predicate as `BasicCutResolutionAtBreakpoints`). This is the
--   mirror of `BasicCutResolutionAtBreakpoints` on the other component, and — unlike that lemma, which
--   bounds a `smallPieceCount` via an infimum over resolutions — gives an *exact* piece count, since
--   `IsPiecewiseGeodesicWith` only asserts existence of a resolution with the stated number of
--   pieces.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedResolution.lean#L22-L159
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedResolution.lean#L22-L159

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_RestrictPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_RestrictPiecewiseGeodesic

set_option autoImplicit false
open Set

theorem BasicCutDiscardedResolution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (k : ℕ) (s : ℕ → ℝ)
    (hres : IsGeodesicResolution γ k s) (p q : ℕ) (hp : p ≤ k) (hq : q ≤ k)
    (hne : s p ≠ s q)
    (ht0 : 0 ≤ s p) (htlen : s p ≤ γ.len) (ht'0 : 0 ≤ s q) (ht'len : s q ≤ γ.len) :
    IsPiecewiseGeodesicWith (BasicCut GP γ hclosed (s p) (s q) ht0 htlen ht'0 ht'len).2
      (((Finset.Icc 1 k).filter (fun j =>
          if p < q then p < j ∧ j ≤ q else j ≤ q ∨ p < j)).card + 1) := by sorry
