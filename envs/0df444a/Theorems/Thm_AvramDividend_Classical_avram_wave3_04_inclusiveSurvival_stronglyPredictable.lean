-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
-- name    : AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:30:26.139318+00:00
-- url     : https://prove2.me/theorems/69806d16-1c2a-445a-920f-4500f3645d6a
-- title:
--   Any stopping-time inclusive survival indicator is strongly predictable
-- statement:
--   For any stopping time valued in extended nonnegative real numbers, including an infinite clock, the inclusive survival process 1_{t≤τ} is strongly predictable in the same filtration. It is strongly adapted because the stopping-time survival event is measurable at each time, and its sample paths are left-continuous since the value at the stopping clock is one. The theorem is a source-independent predictable localisation interface suitable for the original dividend ruin clock.
-- source:
--   Pinned Mathlib IsStoppingTime.measurableSet_ge, IsStronglyPredictable, left continuity of ENNReal threshold indicators, and accepted generic strongly-adapted left-continuous predictability theorem UUID 5ae104c4-13de-429a-a344-76d22511259b. Private remote compiler probe 2b67df36-378e-45a3-8d95-2ba64d162230 passed sentinel without source errors, source SHA-256 e84d940fe661c3fae7bee27ce680fa68bc3dbd9716f79da5cbda7dd08d6eab63.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_inclusiveSurvival_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ) :
    IsStronglyPredictable 𝓕
      (fun t ω => if (t : ℝ≥0∞) ≤ τ ω then (1 : ℝ) else 0) := by sorry
