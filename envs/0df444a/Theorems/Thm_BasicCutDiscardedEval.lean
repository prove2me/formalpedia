-- Prove2me | Theorems.Thm_BasicCutDiscardedEval
-- name    : BasicCutDiscardedEval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:11:47.907194+00:00
-- url     : https://prove2.me/theorems/66a0a9f1-f8c0-4605-9666-e3c3e44f17f9
-- title:
--   Basic Cut Discarded Eval: Basic Cut Discarded Eval
-- statement:
--   The pointwise description of the discarded output `g` of a basic cut `C(γ,t,t')`
--   (`BasicCut`), which is by construction the concatenation of the circular arc
--   `A := γ|_{[t,t']}` (`curveArc`) with the single closing geodesic edge
--   `C := G_{γ(t'),γ(t)}` (`GeodesicPairing`): its length is `len(A)+len(C)`, it agrees with `A`
--   throughout `A`'s own parameter interval `[0,len(A)]`, and on the remaining interval
--   `[len(A),len(g)]` it is a geodesic (`IsGeodesicOn`), being a translate of the geodesic `C`.
--   This is the description needed to splice a Morrey decomposition of `A` back into one of `g`:
--   `BasicCutLength` records `len(g)` only in the `(if t ≤ t' then t'-t else (γ.len-t)+t') + dist`
--   form and says nothing about the values of `g`, and `BasicCutDiscardedResolutionGeneral` records
--   only the *existence* of a geodesic resolution of `g`, with no identification of its pieces with
--   `A`'s.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedEval.lean#L25-L85
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutDiscardedEval.lean#L25-L85

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_CurveConcatEndpoints
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsClosedCurve
import Definitions.Def_Tablet_IsGeodesicOn
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveConcat
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_BasicCutDiscardedEval
import Theorems.Thm_CurveConcatEndpoints

set_option autoImplicit false
open Set

theorem BasicCutDiscardedEval {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (γ : Curve E) (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len)
    (ht'0 : 0 ≤ t') (ht'len : t' ≤ γ.len) :
    (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len
        = (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
          + (GP.G (γ.toFun t') (γ.toFun t)).len ∧
      (∀ v : ℝ, v ≤ (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len →
        (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.toFun v
          = (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).toFun v) ∧
      IsGeodesicOn (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2
        (curveArc γ hclosed t t' ht0 htlen ht'0 ht'len).len
        (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2.len := by sorry
