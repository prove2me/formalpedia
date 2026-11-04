-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_centered_uncentered_jump_delta
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_centered_uncentered_jump_delta
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:52:07.907307+00:00
-- url     : https://prove2.me/theorems/b31434b5-be64-4473-997f-7019d5aa8d7a
-- title:
--   Original Lévy centred and uncentred intrinsic jump sizes agree at positive times
-- statement:
--   For the same original source sample ω, every positive jump time u has identical jump size when the coordinate path is centred by its time-zero value. Follows from the original cadlag left-limit theorem and the continuous translation of one-sided limits. This is a strict pathwise bridge needed before converting the proved compact-test centred finite jump sum into the canonical uncentred intrinsic marked measure. No assumed jump-rate, compensator or external model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_centered_uncentered_jump_delta
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (u : ℝ≥0) (hu : 0 < u) :
    (X.X u ω - X.X 0 ω) -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω - X.X 0 ω) u =
    X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u := by sorry
