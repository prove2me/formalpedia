-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:16:21.997515+00:00
-- url     : https://prove2.me/theorems/537a4fa4-1024-41af-be63-fd51b2971ce1
-- title:
--   Original BV signed raw negative left-jump cumulative real sum is monotone
-- statement:
--   The exact real cumulative sum of observed original negative left-jump magnitudes, with no ENNReal coercion left in the conclusion, is nondecreasing in source time almost surely. Follows from the accepted monotonicity of the finite ENNReal magnitude sum and its accepted equality to the actual raw real jump series on every interval.
-- source:
--   Proved 0759bddb-d4be-428b-8f10-2e8f94910777 and f0ec726b-b68a-4a0f-a3b3-86166ccd2bfd; no novel process model.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 =>
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by sorry
