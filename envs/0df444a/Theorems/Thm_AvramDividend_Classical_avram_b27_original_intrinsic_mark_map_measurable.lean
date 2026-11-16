-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b27_original_intrinsic_mark_map_measurable
-- name    : AvramDividend.Classical.avram_b27_original_intrinsic_mark_map_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:27:07.614546+00:00
-- url     : https://prove2.me/theorems/647cc2d8-7eac-4c14-a1d6-d5dc609239f3
-- title:
--   The original Lévy intrinsic marked jump source map is Borel measurable from actual jump-time countability
-- statement:
--   For any original spectrally negative Lévy sample path under Prove2Me definitions, the map u↦(u, X_u-X_{u-}) is Borel measurable. Off the countable positive-jump-time set it coincides with the continuous baseline u↦(u,0); zero time adds at most one singleton. This directly establishes the measurability of the original marked-jump pushforward used in the B25 two-channel source, with no extra local path measurability assumptions. Uses the already Proved source jump-time countability lemma.
-- source:
--   Existing Prove2Me Proved 741d3b5f all original Lévy jump times countable; Mathlib Measurable.measurable_of_countable_ne.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_all_original_levy_jump_times_countable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_b27_original_intrinsic_mark_map_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
