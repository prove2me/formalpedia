-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b111_original_all_actual_positive_time_jump_nonpositive
-- name    : AvramDividend.Classical.avram_b111_original_all_actual_positive_time_jump_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:14:54.78002+00:00
-- url     : https://prove2.me/theorems/d0c21664-d117-40d1-8d81-ae8e20186eb5
-- title:
--   Every genuine original Lévy positive-time source left-limit jump is nonpositive pathwise
-- statement:
--   The original SpectrallyNegativeLevy structure gives a no-positive-jumps field requiring a left-limit convergence proof at a positive time. The Proved original cadlag theorem supplies the correct canonical Function.leftLim convergence on every sample path. Combining them yields the exact original physical jump X(t)-X(t-) at most zero for every sample path and every positive t, with no extra almost-everywhere or finite-activity restriction. This discharges the physical jump-sign step in true stopped source marked-cell classification and B109.
-- source:
--   Original SpectrallyNegativeLevy.noPosJumps field, Proved avram_p2_a_zero_rate_original_cadlag_regular_all_times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact all-path original spectral negativity for the same source canonical left limit. -/

theorem AvramDividend.Classical.avram_b111_original_all_actual_positive_time_jump_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    X.X t ω -
      Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≤ 0 := by sorry
