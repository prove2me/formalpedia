-- Prove2me | Theorems.Thm_CurveCurrentMeasurable
-- name    : CurveCurrentMeasurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:48.470936+00:00
-- url     : https://prove2.me/theorems/039e0c5d-411c-43e6-b567-3eb981181273
-- title:
--   Curve Current Measurable: Curve Current Measurable
-- statement:
--   The current `γ ↦ [[γ]](ω)` of a fixed metric `1`-form `ω` is measurable in `γ` (with `Θ(E)`
--   carrying the evaluation `σ`-algebra of `CurveMeasurableSpace`). This is the measurability fact
--   paper.tex line 1290 asserts without proof for the countable family `γ ↦ [[γ]](f,π)` feeding
--   `SLLNCurves`; `PSFamily.weakLength` does not itself supply it. The proof samples `γ` at the
--   uniform partition `s_i = i·γ.len/m` to build a Riemann sum `R m`, shows each `R m` is measurable
--   (from `CurveScaledEvalMeasurable`), shows `R m γ → [[γ]](ω)` (from `CurrentResolutionAdditive`,
--   `RestrictCurrentFormula`, and `CurrentChordEstimate` summed over the partition), and concludes by
--   `measurable_of_tendsto_metrizable`.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveCurrentMeasurable.lean#L21-L158
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/CurveCurrentMeasurable.lean#L21-L158

import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Definitions.Def_Tablet_CurveCurrentBound
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_Form1
import Definitions.Def_Tablet_CurveCurrentMeasurable
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveCurrentBound
import Theorems.Thm_CurveScaledEvalMeasurable
import Theorems.Thm_RestrictCurrentFormula

set_option autoImplicit false
open MeasureTheory Finset

theorem CurveCurrentMeasurable {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (ω : Form1 E) : Measurable (fun g : Curve E => curveCurrent g ω) := by sorry
