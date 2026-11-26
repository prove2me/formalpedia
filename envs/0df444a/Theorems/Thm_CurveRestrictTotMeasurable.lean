-- Prove2me | Theorems.Thm_CurveRestrictTotMeasurable
-- name    : CurveRestrictTotMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:58.683019+00:00
-- url     : https://prove2.me/theorems/90d8cb9d-68ab-4eb9-91a0-fc75880ebe30
-- title:
--   Curve Restrict Tot Measurable: Curve Restrict Tot Measurable
-- statement:
--   The Curve Restrict Tot Measurable construction uses the Curve Restrict Tot Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveRestrictTotMeasurable.lean#L7-L29
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveRestrictTotMeasurable.lean#L7-L29

import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveEvalJointMeasurable
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveRestrictTotMeasurable
import Theorems.Thm_CurveEvalJointMeasurable
import Theorems.Thm_CurveLenMeasurable

set_option autoImplicit false

theorem CurveRestrictTotMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (a b : ℝ) : Measurable (fun γ : Curve E => curveRestrictTot γ a b) := by sorry
