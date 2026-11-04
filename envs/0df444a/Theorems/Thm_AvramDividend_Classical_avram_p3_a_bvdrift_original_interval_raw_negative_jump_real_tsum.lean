-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:32:45.828674+00:00
-- url     : https://prove2.me/theorems/f0ec726b-b68a-4a0f-a3b3-86166ccd2bfd
-- title:
--   Actual original BV raw real negative jump magnitudes are summable with exact full total
-- statement:
--   On a single original P-almost-sure event for a bounded-variation spectrally negative Levy process, every ordered finite interval has a convergent real series of genuine signed raw left-jump magnitudes leftLim X - X, and its sum equals the full intrinsic original ENNReal negative-jump total converted to real. All assumptions concern only the given source X.
-- source:
--   Combine independently Proved original real ENNReal source summability and source no-positive-jump exact ofReal-toReal conversion, pointwise on interval support; then rewrite the summand function under Summable and tsum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_jump_summable_and_tsum
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_left_jump_nonnegative_and_toReal

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- On every actual BV interval, the signed real source left-jump magnitudes
form a summable series equal to the full genuine ENNReal jump total. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      Summable (fun u : ℝ≥0 => if s < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0) ∧
      (∑' u : ℝ≥0,
        if s < u ∧ u ≤ t then ENNReal.ofReal (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω) else 0).toReal =
        ∑' u : ℝ≥0, if s < u ∧ u ≤ t then Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0 := by sorry
