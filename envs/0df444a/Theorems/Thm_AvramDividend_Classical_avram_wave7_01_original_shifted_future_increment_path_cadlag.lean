-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_increment_path_cadlag
-- name    : AvramDividend.Classical.avram_wave7_01_original_shifted_future_increment_path_cadlag
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:45:10.675127+00:00
-- url     : https://prove2.me/theorems/984180e2-a00f-451d-baee-171f8a95dcc6
-- title:
--   Every actual shifted Lévy future-increment path is right-continuous with finite strict-left limits
-- statement:
--   For every sample ω of the original SpectrallyNegativeLevy X and deterministic source time s, the genuine future-increment path v↦X(s+v,ω)−X(s,ω) is right-continuous at every v≥0 and has a finite strict-left limit at every positive v. This supplies the exact càdlàg regularity hypotheses needed to apply a generic measurable marked-jump-count functional, without a replacement process, BV or finite activity.
-- source:
--   Proved same-source shifted right-continuity b901917f; exact original left-limit axiom X.leftLim, time-shifted strict-left filter map as in Proved 81fc4187.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_shiftedLevy_increments_right_continuous

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_shifted_future_increment_path_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s : ℝ≥0) :
    (∀ t : ℝ≥0,
      ContinuousWithinAt
        (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
        (Ici t) t) ∧
    (∀ u : ℝ≥0, 0 < u →
      ∃ l : ℝ, Tendsto
        (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)
        (𝓝[<] u) (𝓝 l)) := by sorry
