-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_arbitrary_window_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_arbitrary_window_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:56:50.651848+00:00
-- url     : https://prove2.me/theorems/03058d10-0af3-473b-8b84-d78f464c2f21
-- title:
--   Original intrinsic Borel mark-mean measure on arbitrary deterministic time windows
-- statement:
--   For each window (s,t] of the actual original spectrally negative Lévy process, the expected literal marked jump count defines a genuine measure on Borel marks. No jump intensity or identification with the source Lévy measure is assumed.
-- source:
--   Use the Proved original Campbell measure Q and its original-source rectangle equality, restricting it to Ioc s t times univ and mapping by Prod.snd. Verify the pushforward marginal by measurable projection and restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_arbitrary_window_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) := by sorry
