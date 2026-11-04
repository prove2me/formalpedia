-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_unit_time_mark_mean_measure
-- name    : AvramDividend.Classical.avram_p2_d_future_original_unit_time_mark_mean_measure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T17:50:36.92421+00:00
-- url     : https://prove2.me/theorems/32d3702f-6688-4d7a-8190-7475ce004cc2
-- title:
--   Original time-one expected intrinsic marked jumps define an actual mark measure
-- statement:
--   On the unchanged original probability space and spectrally negative Lévy path, there exists a genuine measure on real marks whose value on each Borel B is exactly the expected literal original jump count on (0,1]×B, even with infinite activity. This source Campbell mark measure is not yet identified with the Lévy measure ν.
-- source:
--   Use the Proved original past-event Campbell measure Q for s=0 and A=univ, restrict Q to the first physical unit-time strip, map along Prod.snd, and verify the mark marginal using Measure.map_apply, Measure.restrict_apply and Q's exact source counting identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_original_unit_time_mark_mean_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      ρ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by sorry
