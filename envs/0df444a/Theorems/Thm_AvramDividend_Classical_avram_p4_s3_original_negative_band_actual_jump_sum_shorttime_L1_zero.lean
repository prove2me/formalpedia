-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_actual_jump_sum_shorttime_L1_zero
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_shorttime_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:27:29.531568+00:00
-- url     : https://prove2.me/theorems/d1706a16-a74f-4a08-b423-c34a3d0569ac
-- title:
--   Actual negative-band physical jump-time sum collision error vanishes on shrinking horizons
-- statement:
--   For the original Lévy physical negative-band marked times up to T/k, an arbitrary bounded path-and-time dependent kernel has a multiple-jump sum whose L1 norm expectation vanishes as k grows, assuming the sum is measurable. The quantitative rate is at most B*(T ν_band/k)^2, with no equality-in-law or artificial jump count.
-- source:
--   Public P4-S3 actual physical jump sum L1 bound 7503e7fb and public physical horizon intensity rate c3093fe5.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_shorttime_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (f : ℕ → Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ k ω u, |f k ω u| ≤ B)
    (hErrMeas : ∀ k : ℕ, AEStronglyMeasurable (fun ω =>
      if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ T / (k : ℝ≥0) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (T / (k : ℝ≥0)) n).toFinset, f k ω u
      else 0) P) :
    let F : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite
        X ω (T / (k : ℝ≥0)) n).toFinset
    let K : ℕ → Ω → ℕ := fun k ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T / (k : ℝ≥0) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, ‖if 2 ≤ K k ω then ∑ u ∈ F k ω, f k ω u else 0‖ ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry
