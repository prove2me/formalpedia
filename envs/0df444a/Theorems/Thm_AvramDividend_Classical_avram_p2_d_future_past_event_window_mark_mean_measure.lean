-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_past_event_window_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_past_event_window_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:03:51.282762+00:00
-- url     : https://prove2.me/theorems/f42064b2-64b7-43b3-965d-ef5454627aaa
-- title:
--   Original past-event marked jump mean defines a Borel mark measure on future windows
-- statement:
--   For every event measurable at the past time s, the original intrinsic jump-count expectation restricted to that event and window (s,t] defines a genuine measure in the Borel mark variable. This is the source-side mark measure needed for compensator steps and does not assume ν intensity.
-- source:
--   Apply the Proved original past-event Campbell occupation measure with the actual X, s, A. Restrict to Ioc s t times the whole mark space and project under Prod.snd; verify map/restrict sets against the Proved exact Q_A(C) equality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_past_event_window_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      ρ B = (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by sorry
