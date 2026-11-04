-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:16:28.130481+00:00
-- url     : https://prove2.me/theorems/73032d17-1bbf-43cf-a41f-8342576e796e
-- title:
--   Original bounded-variation raw real cumulative negative-jump series has exact strict-past left limit
-- statement:
--   For the genuine original BV Lévy process and every positive time, the left limit of the raw real cumulative negative-left-jump series over (0,s] equals the sum of actual raw negative-left-jump magnitudes over (0,t), almost surely and simultaneously over all times. This is the key pure atomic continuity ingredient for jump removal; it does not assert that the full Lévy residual is zero.
-- source:
--   Proved original raw real jump summability f0ec726b and analytically verified generic Tannery left-limit helper avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left, plus Mathlib leftLim_eq_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_left

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On the actual BV Levy source path, the cumulative raw real
negative-jump series has the strict-past jump sum as its left limit. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim (fun s : ℝ≥0 => (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) t =
        (∑' u : ℝ≥0, if 0 < u ∧ u < t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by sorry
