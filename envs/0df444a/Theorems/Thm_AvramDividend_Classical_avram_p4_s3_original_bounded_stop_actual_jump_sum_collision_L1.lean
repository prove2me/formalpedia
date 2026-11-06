-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L1
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:04:14.525475+00:00
-- url     : https://prove2.me/theorems/4b36f9df-8de6-4425-8e04-85aab899f27d
-- title:
--   Actual original stopped negative-band physical jump-time sum has quadratic collision L1 error
-- statement:
--   For the original stopped physical marked negative-band times at any path-dependent τ≤T, a uniformly bounded random time-indexed kernel has an integrable multiple-jump sum with expected norm at most B(Tν_band)², assuming measurability of the stopped count and error sum. This is a source-exact stopped finite-band L1 bound.
-- source:
--   Original finite marked negative jump times at the sample-dependent clock, cardinality equality, and bounded-clock quadratic collision expected count theorem.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard))
    (f : Ω → ℝ≥0 → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ ω u, |f ω u| ≤ B)
    (hErrMeas : AEStronglyMeasurable (fun ω =>
      if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (τ ω) n).toFinset, f ω u
      else 0) P) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n).toFinset
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) P ∧
    (∫ ω, ‖if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0‖ ∂P) ≤ B * r ^ 2 := by sorry
