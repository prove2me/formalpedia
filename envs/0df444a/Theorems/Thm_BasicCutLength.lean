-- Prove2me | Theorems.Thm_BasicCutLength
-- name    : BasicCutLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:06:00.279781+00:00
-- url     : https://prove2.me/theorems/987862d2-d75a-48ba-bc4c-001ee7a73ffa
-- title:
--   Basic Cut Length: Basic Cut Length
-- statement:
--   The lengths of `BasicCut`'s two outputs, and the closing-edge-vs-arc-length comparison that
--   makes them meaningful: writing `A` for the length of the excised arc `γ|_{[t,t']}` (ordinary if
--   `t ≤ t'`, wrap-around if `t' < t`) and `d` for the length `dist (γ.toFun t) (γ.toFun t')` of the
--   single closing geodesic edge, the kept output has length `γ.len - A + d` and the discarded output
--   has length `A + d`, and `d ≤ A`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutLength.lean#L15-L70
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutLength.lean#L15-L70

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutLength
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open Set

theorem BasicCutLength {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t')
    (ht'len : t' ≤ γ.len) (hne : t ≠ t') :
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1.len
        = γ.len - (if t ≤ t' then t' - t else (γ.len - t) + t')
          + dist (γ.toFun t) (γ.toFun t') ∧
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len
        = (if t ≤ t' then t' - t else (γ.len - t) + t') + dist (γ.toFun t) (γ.toFun t') ∧
    dist (γ.toFun t) (γ.toFun t') ≤ (if t ≤ t' then t' - t else (γ.len - t) + t') := by sorry
