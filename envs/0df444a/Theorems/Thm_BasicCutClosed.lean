-- Prove2me | Theorems.Thm_BasicCutClosed
-- name    : BasicCutClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:07:59.166311+00:00
-- url     : https://prove2.me/theorems/cf431185-1d31-4c8b-9e82-4b02bbfc2dfb
-- title:
--   Basic Cut Closed: Basic Cut Closed
-- statement:
--   Both outputs of `BasicCut γ t t'` (for `t ≠ t'`) are closed, piecewise-geodesic curves,
--   provided `γ` itself is closed and piecewise-geodesic (paper.tex lines 581-583).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutClosed.lean#L20-L98
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutClosed.lean#L20-L98

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_ArcGeodesicResolution
import Definitions.Def_Tablet_BasicCutDiscardedResolutionGeneral
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_IsPiecewiseGeodesic
import Definitions.Def_Tablet_IsGeodesicResolution
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_BasicCutClosed
import Theorems.Thm_ArcGeodesicResolution
import Theorems.Thm_BasicCutDiscardedResolutionGeneral
import Theorems.Thm_CurveConcatEndpoints

set_option autoImplicit false
open Set

theorem BasicCutClosed {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (hpg : IsPiecewiseGeodesic γ) (t t' : ℝ)
    (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) (hne : t ≠ t') :
    IsClosedCurve (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ∧
      IsPiecewiseGeodesic (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ∧
      IsClosedCurve (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 ∧
      IsPiecewiseGeodesic (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 := by sorry
