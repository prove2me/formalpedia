-- Prove2me | Theorems.Thm_CurveLenMeasurable
-- name    : CurveLenMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:50:23.39047+00:00
-- url     : https://prove2.me/theorems/fbef54b3-e942-4676-8fe3-b7bcb60a9afc
-- title:
--   Curve Len Measurable: Curve Len Measurable
-- statement:
--   The Curve Len Measurable construction uses the Curve Len Measurable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveLenMeasurable.lean#L4-L9
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveLenMeasurable.lean#L4-L9

import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveLenMeasurable
set_option autoImplicit false

theorem CurveLenMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] :
    Measurable (fun γ : Curve E => γ.len) := by sorry
