-- Prove2me | Theorems.Thm_CurveEvalJointMeasurable
-- name    : CurveEvalJointMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:28.40041+00:00
-- url     : https://prove2.me/theorems/15881ba3-c7b8-467a-93b8-febb14736230
-- title:
--   Curve Eval Joint Measurable: Curve Eval Joint Measurable
-- statement:
--   The Curve Eval Joint Measurable construction uses the Curve Eval Joint Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveEvalJointMeasurable.lean#L8-L16
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveEvalJointMeasurable.lean#L8-L16

import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveLipschitz
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Definitions.Def_Tablet_CurveEvalJointMeasurable
import Theorems.Thm_CurveLipschitz

set_option autoImplicit false
open MeasureTheory

theorem CurveEvalJointMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (Function.uncurry (fun (t : ℝ) (γ : Curve E) => γ.toFun t)) := by sorry
