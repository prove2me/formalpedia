-- Prove2me | Theorems.Thm_CurveRestrictTotAgrees
-- name    : CurveRestrictTotAgrees
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:29.432796+00:00
-- url     : https://prove2.me/theorems/8fab866f-6f73-4f73-8e9f-33628263719e
-- title:
--   Curve Restrict Tot Agrees: Curve Restrict Tot Agrees
-- statement:
--   The Curve Restrict Tot Agrees construction uses the Curve Restrict Tot Agrees property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveRestrictTotAgrees.lean#L5-L24
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveRestrictTotAgrees.lean#L5-L24

import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_CurveRestrictTotAgrees
set_option autoImplicit false

theorem CurveRestrictTotAgrees {E : Type*} [MetricSpace E] (γ : Curve E) (a b : ℝ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len) :
    curveRestrictTot γ a b = curveRestrict γ a b ha hab hb := by sorry
