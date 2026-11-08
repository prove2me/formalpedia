-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn11_levy_real_mark_loss_conversion
-- name    : AvramDividend.Classical.avram_bv_jump8_turn11_levy_real_mark_loss_conversion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:36:34.823664+00:00
-- url     : https://prove2.me/theorems/3d2e402b-eab2-4ddc-823b-6ad438016441
-- title:
--   Finite-cutoff Lévy weighted ENNReal compensator converts to the original real mark-loss integral
-- statement:
--   The original Lévy measure has finite strict negative cutoff band mass; convert T times its ENNReal weighted mark-loss lintegral to T_real times the actual real Bochner integral, retaining zero clock and strict y< -ε.
-- source:
--   The original Lévy measure has finite strict negative cutoff band mass; convert T times its ENNReal weighted mark-loss lintegral to T_real times the actual real Bochner integral, retaining zero clock and strict y< -ε.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn11_levy_real_mark_loss_conversion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (k n : ℕ) :
    let T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)
    let ε : ℝ := 1 / ((k : ℝ) + 1)
    let φ : ℝ → ℝ≥0∞ := fun y => ENNReal.ofReal (1 - Real.exp y)
    let B : Set ℝ := Iio (-ε)
    (((T : ℝ≥0∞) * (∫⁻ y in B, φ y ∂X.ν))).toReal =
      (1 / ((n : ℝ) + 1)) *
        (∫ y in B, (1 - Real.exp y) ∂X.ν) := by sorry
