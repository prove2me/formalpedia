-- Prove2me | Theorems.Thm_BasicCutResolutionGeneral
-- name    : BasicCutResolutionGeneral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:57.565834+00:00
-- url     : https://prove2.me/theorems/e1089a1f-8e1c-5fc1-9343-c650fb6df312
-- title:
--   Basic Cut Resolution General: Basic Cut Resolution General
-- statement:
--   For a closed, piecewise-geodesic curve `γ` and arbitrary (not necessarily breakpoint) cut
--   points `t ≠ t'`, the kept output `γ'` of `BasicCut γ t t'` has at most `3` more small (length
--   `< δ`) edges, in the `smallPieceCount` sense, than `γ` itself. Unlike `BasicCutResolutionAtBreakpoints`,
--   this places no hypothesis on `t,t'` beyond membership in `[0,len(γ)]` and `t ≠ t'`: it is the form
--   paper Lemma 3.8's cut points -- which attain an infimum over arbitrary reals, not over the
--   breakpoints of any fixed resolution -- actually need.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutResolutionGeneral.lean#L22-L191
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutResolutionGeneral.lean#L22-L191

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_smallPieceCount
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_ConcatGeodesicResolution
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_ShiftedBreakpointShortEdgeCount
import Definitions.Def_Tablet_SplicedBreakpointShortEdgeCount
import Definitions.Def_Tablet_BasicCutResolutionGeneral
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_ConcatGeodesicResolution
import Theorems.Thm_CurveConcatEndpoints
import Theorems.Thm_GeodesicIsPiecewiseGeodesic
import Theorems.Thm_ShiftedBreakpointShortEdgeCount
import Theorems.Thm_SplicedBreakpointShortEdgeCount

set_option autoImplicit false
open Set

theorem BasicCutResolutionGeneral {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) (δ : ℝ) (hδ : 0 < δ)
    (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len)
    (hne : t ≠ t') :
    smallPieceCount (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 δ
      ≤ smallPieceCount γ δ + 3 := by sorry
