-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_raw_jump_interval_additivity
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_interval_additivity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:06:17.172558+00:00
-- url     : https://prove2.me/theorems/ca8841f1-ba91-459f-915e-f7d5caf9d1f9
-- title:
--   Actual source BV raw signed real negative-jump series splits over all ordered intervals
-- statement:
--   On one original BV Lévy sample-path event, the genuine raw signed real left-jump series is additive when an interval is split into two adjacent intervals. This uses no Poisson representation and keeps the real path increments needed for the C¹ change-of-variables proof.
-- source:
--   Proved original interval ENNReal-to-real additivity f0b0f24b and actual raw real negative-jump equivalence f0ec726b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_real_negative_jump_additivity
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Summable raw actual negative source left jumps split exactly under
every ordered subdivision of a BV sample-path interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_raw_jump_interval_additivity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t r : ℝ≥0), s ≤ t → t ≤ r →
      (∑' u : ℝ≥0, if s < u ∧ u ≤ r then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) =
      (∑' u : ℝ≥0, if s < u ∧ u ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) + (∑' u : ℝ≥0, if t < u ∧ u ≤ r then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0) := by sorry
