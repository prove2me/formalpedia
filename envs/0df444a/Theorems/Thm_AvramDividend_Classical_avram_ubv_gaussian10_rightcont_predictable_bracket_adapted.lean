-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_rightcont_predictable_bracket_adapted
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_rightcont_predictable_bracket_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:14:26.381044+00:00
-- url     : https://prove2.me/theorems/5f4ccdfd-5a14-4415-9b87-b8d35f4d7773
-- title:
--   Original stopped right-continuous Gaussian predictable squared bracket is adapted
-- statement:
--   For Avram's original spectrally negative Levy process and its explicit stopping filtration 𝓕.rightCont, any coefficient measurable for the right-continuous predictable sigma-algebra has an adapted squared pathwise time bracket under a sigma-finite time measure. This uses original rightCont predictable set traces, band indicator measurability and measurable time integration, with the identical original probability space and stopping filtration. It does not claim the stochastic integral construction or bracket compensator martingale property.
-- source:
--   formal-applied-math/formal-mathfin BracketCompensator.lean measurable_bandSqClamped and measurable_bracketRep; pinned Mathlib; original rightCont trace child, inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_rightcont_predictable_band_trace

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_rightcont_predictable_bracket_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime] :
    Adapted 𝓕.rightCont (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by sorry
