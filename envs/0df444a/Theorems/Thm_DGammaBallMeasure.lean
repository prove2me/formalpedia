-- Prove2me | Theorems.Thm_DGammaBallMeasure
-- name    : DGammaBallMeasure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:08:43.739331+00:00
-- url     : https://prove2.me/theorems/91bbd606-1fbd-5c44-966a-24e6c6cbba45
-- title:
--   DGamma Ball Measure: DGamma Ball Measure
-- statement:
--   The set of parameters within circle distance `ρ` of `s` has Lebesgue measure at most `2ρ`.
--   This is the step Lemma 3.4's proof leaves implicit (paper.tex line 702). The hypothesis
--   `s ∈ [0, γ.len]` is necessary: `dGamma` is not clamped in its arguments, so for `s` outside
--   `[0, γ.len]` the claim is false.
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DGammaBallMeasure.lean#L10-L82
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/DGammaBallMeasure.lean#L10-L82

import Definitions.Def_Tablet_dGamma
import Definitions.Def_Tablet_DGammaBallMeasure
set_option autoImplicit false
open MeasureTheory Set ENNReal

theorem DGammaBallMeasure {E : Type*} [MetricSpace E] (γ : Curve E) (s ρ : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) γ.len) (hρ : 0 < ρ) :
    volume { t ∈ Set.Icc (0 : ℝ) γ.len | dGamma γ s t < ρ } ≤ ENNReal.ofReal (2 * ρ) := by sorry
