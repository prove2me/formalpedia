-- Prove2me | Theorems.Thm_BasicCutDiscardedResolutionGeneral
-- name    : BasicCutDiscardedResolutionGeneral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:04:39.251365+00:00
-- url     : https://prove2.me/theorems/83ec10e3-a56f-4c37-9dc1-2f8ce9a989b9
-- title:
--   Basic Cut Discarded Resolution General: Basic Cut Discarded Resolution General
-- statement:
--   For arbitrary (not necessarily breakpoint) cut points `t,t'`, if the circular arc
--   `γ|_{[t,t']}` (`curveArc`) admits any geodesic resolution with `kA` edges, then the discarded
--   output `g` of `BasicCut` admits an exact geodesic resolution with `kA+1` edges: the arc's own
--   resolution plus the one new closing geodesic edge. Unlike `BasicCutDiscardedResolution` (which is
--   tied to cut points that are breakpoints of a fixed resolution of `γ`), this holds uniformly for
--   every `t,t' ∈ [0,len(γ)]` with `t ≠ t'`, with no case split on their order beyond the one already
--   internal to `curveArc`, since `BasicCut`'s discarded output is *always* `curveArc γ t t'` closed by
--   one geodesic edge, regardless of the order of `t,t'`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedResolutionGeneral.lean#L21-L84
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedResolutionGeneral.lean#L21-L84

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_GeodesicIsPiecewiseGeodesic

set_option autoImplicit false
open Set

theorem BasicCutDiscardedResolutionGeneral {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len)
    (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) (hne : t ≠ t')
    (kA : ℕ) (sA : ℕ → ℝ)
    (hresA : IsGeodesicResolution (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len) kA sA) :
    IsPiecewiseGeodesicWith (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 (kA + 1) := by sorry
