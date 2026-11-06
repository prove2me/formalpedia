-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_stopped_actual_jump_sum_shorttime_L1_zero
-- name    : AvramDividend.Classical.avram_p4_s3_original_stopped_actual_jump_sum_shorttime_L1_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:18:58.86632+00:00
-- url     : https://prove2.me/theorems/f1ef078a-7d17-462c-8c1d-2a0a9064d205
-- title:
--   Original stopped physical negative-band jump-time sum has vanishing L1 collision error under shrinking envelopes
-- statement:
--   Original path-dependent stopping times τ_k≤T/k, measurable negative-band counts and bounded time-dependent original jump kernel f_k imply the expected L1 mass of the two-or-more-jump collision sum tends to zero; quantitative bound B(Tνband/k)^2 for positive k.
-- source:
--   Accepted bounded original stopped physical marked-time collision L1 theorem and the proved original intensity horizon rate.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_stopped_actual_jump_sum_shorttime_L1_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : ℕ → Ω → ℝ≥0)
    (hτBound : ∀ k ω, τ k ω ≤ T / (k : ℝ≥0))
    (hKmeas : ∀ k : ℕ, Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard))
    (f : ℕ → Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ k ω u, |f k ω u| ≤ B)
    (hErrMeas : ∀ k : ℕ, AEStronglyMeasurable (fun ω =>
      if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (τ k ω) n).toFinset, f k ω u
      else 0) P) :
    let F : ℕ → Ω → Finset ℝ≥0 := fun k ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite
        X ω (τ k ω) n).toFinset
    let K : ℕ → Ω → ℕ := fun k ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ k ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    Filter.Tendsto (fun k : ℕ =>
      ∫ ω, ‖if 2 ≤ K k ω then ∑ u ∈ F k ω, f k ω u else 0‖ ∂P)
      Filter.atTop (nhds (0 : ℝ)) := by sorry
