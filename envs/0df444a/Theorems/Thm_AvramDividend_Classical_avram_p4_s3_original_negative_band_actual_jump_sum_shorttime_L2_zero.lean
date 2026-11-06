-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_actual_jump_sum_shorttime_L2_zero
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_shorttime_L2_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:27:42.921417+00:00
-- url     : https://prove2.me/theorems/4f7abeca-5bc1-435e-93ba-f2bf29bac821
-- title:
--   Actual physical negative-band time-indexed jump sum has vanishing L2 collision error
-- statement:
--   For original physical negative-band marked jump times up to T/k, any uniformly bounded path-dependent time-indexed stochastic kernel has multi-jump squared-error expectation tending to zero, provided the squared finite sum is measurable. Quantitative bound is 2B²(T ν_band/k)² for k>0.
-- source:
--   Public original finite-band actual physical jump sum collision L2 84881d4f and exact physical horizon rate c3093fe5.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_actual_jump_sum_shorttime_L2_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (f : ℕ → Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ k ω u, |f k ω u| ≤ B)
    (hErrSquareMeas : ∀ k : ℕ, AEStronglyMeasurable (fun ω =>
      (if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ T / (k : ℝ≥0) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (T / (k : ℝ≥0)) n).toFinset, f k ω u
      else 0) ^ 2) P) :
    let F : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite
        X ω (T / (k : ℝ≥0)) n).toFinset
    let K : ℕ → Ω → ℕ := fun k ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T / (k : ℝ≥0) ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, (if 2 ≤ K k ω then ∑ u ∈ F k ω, f k ω u else 0) ^ 2 ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry
