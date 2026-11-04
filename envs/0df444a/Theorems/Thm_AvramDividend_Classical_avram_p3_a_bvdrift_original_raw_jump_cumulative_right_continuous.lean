-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T16:02:06.53403+00:00
-- url     : https://prove2.me/theorems/49bf9876-b470-41a3-add7-62af0da071e4
-- title:
--   Original BV source cumulative raw negative left-jump series is right-continuous at all times
-- statement:
--   For the genuine bounded-variation spectrally negative Levy sample path and every t≥0, the full cumulative real negative-jump sum over (0,s] converges from the right to its value at t. Restricts to jumps on (0,t+1] to avoid an infinite-horizon summability hypothesis and uses original BV absolute summability and the pinned right-side Tannery lemma.
-- source:
--   Proved original finite-interval raw real jump summability f0ec726b and separately published generic right-side Tannery dominated convergence lemma. The original source space and jump left limits are unchanged.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_real_atomic_step_tsum_tendsto_right

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual BV source cumulative signed negative-left-jump process
is right-continuous even when its infinite-horizon jump sum diverges. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_right_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Filter.Tendsto (fun s : ℝ≥0 => (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) (𝓝[>] t)
        (nhds (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0)) := by sorry
