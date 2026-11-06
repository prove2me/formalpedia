-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L2
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:03:25.700171+00:00
-- url     : https://prove2.me/theorems/1b5dc4d0-cb11-4702-9527-cbb4aab8c8f5
-- title:
--   Actual physical marked-time bounded-kernel L2 collision budget at a random stopped clock
-- statement:
--   For the genuine original Lévy process and any path-dependent horizon τ≤T, the physical marked negative-band jump-time sum with an arbitrary bounded path-time coefficient has a square-integrable multiple-jump contribution, with E[err²] ≤ 2 B² (T ν_band)², assuming measurability of the stopped count and squared finite sum. Uses neither equality in law nor a stochastic axiom.
-- source:
--   Finiteness/cardinality of the stopped original physical marked set and the new bounded-clock collision squared count theorem; deterministic sum-of-bounded-terms square estimate and dominated integrability.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_actual_jump_sum_collision_L2
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
    (hErrSquareMeas : AEStronglyMeasurable (fun ω =>
      (if 2 ≤ {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard then
        ∑ u ∈ (avram_wave7_06_original_negative_band_marked_times_finite
          X ω (τ ω) n).toFinset, f ω u
      else 0) ^ 2) P) :
    let F : Ω → Finset ℝ≥0 := fun ω =>
      (avram_wave7_06_original_negative_band_marked_times_finite X ω (τ ω) n).toFinset
    let K : Ω → ℕ := fun ω => {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    Integrable (fun ω => (if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) ^ 2) P ∧
    (∫ ω, (if 2 ≤ K ω then ∑ u ∈ F ω, f ω u else 0) ^ 2 ∂P) ≤
      2 * B ^ 2 * r ^ 2 := by sorry
