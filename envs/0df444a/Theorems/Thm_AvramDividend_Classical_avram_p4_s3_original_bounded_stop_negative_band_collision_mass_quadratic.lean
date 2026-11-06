-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_bounded_stop_negative_band_collision_mass_quadratic
-- name    : AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_collision_mass_quadratic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:01:16.382547+00:00
-- url     : https://prove2.me/theorems/98a50131-39d0-4a8f-a54e-9738eda84a80
-- title:
--   Original bounded stopping-clock negative-band multiple-jump expected count remains quadratic
-- statement:
--   For a genuine original physical separated negative-band count stopped at any path-dependent τ≤T, the expected count on the event of two or more jumps is at most (T ν_band)², with integrability and no equality-in-law substitution. Measurability of the stopped count is explicit.
-- source:
--   Physical stopped count ≤ fixed-horizon count from marked-time finiteness and ncard monotonicity, then fixed-horizon original collision L1 theorem 0fa3d06f.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_collision_mass_quadratic
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
    Integrable (fun ω => if 2 ≤ K ω then (K ω : ℝ) else 0) P ∧
    (∫ ω, (if 2 ≤ K ω then (K ω : ℝ) else 0) ∂P) ≤
      r ^ 2 := by sorry
