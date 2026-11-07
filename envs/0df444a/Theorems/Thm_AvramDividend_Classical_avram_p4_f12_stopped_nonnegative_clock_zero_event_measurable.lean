-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
-- name    : AvramDividend.Classical.avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:37:58.928531+00:00
-- url     : https://prove2.me/theorems/1c02c75a-f92f-47f2-bde8-ef1574d9f18f
-- title:
--   Measurable zero-clock event for right-continuous stopped grids
-- statement:
--   The event that a nonnegative random clock is zero is globally measurable whenever its WithTop lifting is a stopping time in the right-continuous filtration. The result supplies the measurable zero-clock set required by stopped process mask and positive-clock excess reductions.
-- source:
--   Prove2Me pinned stopping-time measurable import and original UBV finite-grid stopping-time witness

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    MeasurableSet {ω : Ω | σ ω = 0} := by sorry
