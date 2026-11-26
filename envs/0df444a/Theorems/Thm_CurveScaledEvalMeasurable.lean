-- Prove2me | Theorems.Thm_CurveScaledEvalMeasurable
-- name    : CurveScaledEvalMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:52:36.190308+00:00
-- url     : https://prove2.me/theorems/9d836d68-ff27-498a-b8bf-d49665ee11e9
-- title:
--   Curve Scaled Eval Measurable: Curve Scaled Eval Measurable
-- statement:
--   The Curve Scaled Eval Measurable construction uses the Curve Scaled Eval Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveScaledEvalMeasurable.lean#L5-L9
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveScaledEvalMeasurable.lean#L5-L9

import Definitions.Def_Tablet_CurveEvalJointMeasurable
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Theorems.Thm_CurveEvalJointMeasurable
import Theorems.Thm_CurveLenMeasurable

set_option autoImplicit false

theorem CurveScaledEvalMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) : Measurable (fun γ : Curve E => γ.toFun (c * γ.len)) := by sorry
