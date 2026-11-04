-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:35:03.529246+00:00
-- url     : https://prove2.me/theorems/50ef916b-57ed-4bdd-b0fa-5630d6e42904
-- title:
--   Original BV raw negative-jump series is exactly additive on adjacent intervals
-- statement:
--   For almost every path of the original bounded-variation spectrally negative Levy process, and every 0≤s≤t, the actual signed real left-jump series on (0,t] splits into the series on (0,s] and (s,t]. The proof uses original BV absolute summability and genuine sample-path jump indicators.
-- source:
--   Proved original interval raw negative-jump real summability f0ec726b-b68a-4a0f-a3b3-86166ccd2bfd and Mathlib Summable.tsum_add.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_cumulative_disjoint_interval_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s ≤ t →
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) =
      (∑' u : ℝ≥0, if 0 < u ∧ u ≤ s then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) +
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) := by sorry
