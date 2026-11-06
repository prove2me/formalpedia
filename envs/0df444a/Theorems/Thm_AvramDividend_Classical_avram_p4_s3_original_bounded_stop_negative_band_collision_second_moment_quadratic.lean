-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_collision_second_moment_quadratic
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_collision_second_moment_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:57:52.172532+00:00
-- url     : https://prove2.me/theorems/c6825a5b-b24f-4138-8dee-fd492ff6f46a
-- title:
--   Original bounded random-clock negative-band multiple-jump L2 collision remains quadratic
-- statement:
--   For any path-dependent clock τ≤T and the genuine original physical negative-jump count Kτ in a separated band, the multiple-jump squared count is integrable and has expectation at most 2(T ν_band)², assuming measurability of Kτ. This retains a quadratic collision estimate at the actual stopped path without a Poisson law replacement or bounded stopping-time martingale theorem.
-- source:
--   The original physical random-clock count is pointwise bounded by the original fixed-horizon count using ncard monotonicity and finite marked times. The accepted fixed-horizon quadratic collision second moment cd66a508 provides integrability and the bound.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_collision_second_moment_quadratic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T)
    (hKmeas : Measurable (fun ω : Ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard)) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then (K ω : ℝ) ^ 2 else 0) ∂P) ≤
      2 * r ^ 2 := by sorry
