-- Prove2me | Theorems.Thm_BasicCutCurrent
-- name    : BasicCutCurrent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:05:13.955888+00:00
-- url     : https://prove2.me/theorems/0782cc81-0975-4134-afb0-0ca9e2a322b7
-- title:
--   Basic Cut Current: Basic Cut Current
-- statement:
--   The basic cut splits the current additively: `[[γ]] = [[γ']] + [[g]]` (paper line 585-587),
--   for `t ≠ t'` (the diagonal `t = t'` is excluded: the paper's circular-restriction length identity,
--   paper.tex line 577, is stated only for distinct `t,t'`, and at `t = t'` both outputs of
--   `BasicCut` degenerate to length-`0` curves).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutCurrent.lean#L19-L130
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/BasicCutCurrent.lean#L19-L130

import Definitions.Def_Tablet_BasicCut
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentReverse
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveArc
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveWrapRestrict
import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_BasicCutCurrent
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurrentReverse
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false
open Set

theorem BasicCutCurrent {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (hclosed : IsClosedCurve γ) (t t' : ℝ) (ht0 : 0 ≤ t) (htlen : t ≤ γ.len) (ht'0 : 0 ≤ t')
    (ht'len : t' ≤ γ.len) (hne : t ≠ t') (ω : Form1 E) :
    curveCurrent γ ω = curveCurrent (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).1 ω
      + curveCurrent (BasicCut GP γ hclosed t t' ht0 htlen ht'0 ht'len).2 ω := by sorry
