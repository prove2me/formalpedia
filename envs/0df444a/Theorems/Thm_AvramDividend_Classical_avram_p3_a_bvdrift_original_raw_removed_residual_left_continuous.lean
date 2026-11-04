-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:52:21.182878+00:00
-- url     : https://prove2.me/theorems/41c4b4e0-631c-417b-8a66-dde43c3fb18f
-- title:
--   Original BV drift residual after removing real negative left jumps has no positive-time left discontinuities
-- statement:
--   For the actual original spectrally negative bounded-variation Levy process on its same sample space, removing the genuine real negative jumps from the physical-drift deficit produces a path which agrees with its left limit at each positive time. It may remain a continuous monotone nonzero residual. This uses original X.leftLim, actual jump series, and remote-Proved monotonicity; it does not assume drift identification.
-- source:
--   Previously accepted original real jump summability, cumulative jump monotonicity, generic Tannery left-limit, plus new raw real endpoint split. Combine the original X.leftLim Tendsto, continuity of time drift, Monotone.tendsto_leftLim for actual jump sum, and leftLim_eq_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_leftLim_strict
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_real_jump_total_endpoint_split
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_real_jump_total_monotone_time

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- After removing each actual original BV negative left jump, the genuine
physical-drift residual has no left jumps at positive times. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_removed_residual_left_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t →
      Function.leftLim (fun s : ℝ≥0 =>
        (((s : ℝ) * X.drift - X.X s ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) t = (((t : ℝ) * X.drift - X.X t ω) - (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0)) := by sorry
