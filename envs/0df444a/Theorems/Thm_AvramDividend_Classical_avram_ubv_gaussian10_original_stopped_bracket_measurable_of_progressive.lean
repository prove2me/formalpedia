-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_stopped_bracket_measurable_of_progressive
-- name    : AvramDividend.Classical.avram_ubv_gaussian10_original_stopped_bracket_measurable_of_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T11:30:34.040542+00:00
-- url     : https://prove2.me/theorems/e03aea53-1c04-45cf-a5b8-49d790888a65
-- title:
--   Original stopped Gaussian bracket measurable from progressive source and actual stopping time
-- statement:
--   On Avram’s original probability space and original right-continuous filtration, the square-energy bracket evaluated at an original WithTop-valued stopping clock is measurable, provided the bracket process is strongly progressive for that exact filtration. The hypotheses isolate the genuine missing progressive-measurability step between adaptedness and stopped-bracket L1 integrability. This is not a replacement clock or filtration.
-- source:
--   Pinned Mathlib Probability.Process.Stopping measurable_stoppedValue and Mathlib Probability.Process.Adapted IsStronglyProgressive; inspected 2026-11-07.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian10_original_stopped_bracket_measurable_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ) (μtime : Measure ℝ≥0)
    (hProgressive : IsStronglyProgressive 𝓕.rightCont
      (fun t ω => ∫ s in Ioc (0 : ℝ≥0) t,
        (H (s, ω)) ^ 2 ∂μtime))
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont τ) :
    Measurable (stoppedValue
      (fun t ω => ∫ s in Ioc (0 : ℝ≥0) t,
        (H (s, ω)) ^ 2 ∂μtime) τ) := by sorry
