-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a556_stopped_strict_future_event_measurable
-- name    : AvramDividend.Classical.avram_ga_a556_stopped_strict_future_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:25:47.711119+00:00
-- url     : https://prove2.me/theorems/cf768684-7909-41b4-a3a2-af4280b7cd9f
-- title:
--   Strict-future event of a right-continuous-filtration stopping time is measurable
-- statement:
--   For a nonnegative stopping time with respect to a right-continuous filtration, the strict-future event {omega: s<rho omega} is measurable in the ambient probability space for any deterministic s.
-- source:
--   Complement of the stopping-time event rho<=s, with inclusion of right-continuous filtration sigma-algebra into ambient measurable space

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a556_stopped_strict_future_event_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) (s : ℝ≥0) :
    MeasurableSet {ω : Ω | s < ρ ω} := by sorry
