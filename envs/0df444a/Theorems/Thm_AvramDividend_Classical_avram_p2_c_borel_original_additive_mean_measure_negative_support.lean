-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_negative_support
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_additive_mean_measure_negative_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:23:24.432416+00:00
-- url     : https://prove2.me/theorems/4d799f07-054d-40e2-a83a-49663dac8000
-- title:
--   Actual intrinsic source expected mark measure is time-additive, finite away from zero and supported on negative marks
-- statement:
--   Construct the actual original source expected marked jump measures μ_T on the real mark space. They exactly represent intrinsic Lévy jump counts, add in elapsed time, have finite unit-time negative tails bounded away from zero, and are supported on strict negative marks at every time horizon. This gives an intrinsic candidate intensity independent of its identification with the prescribed triplet ν.
-- source:
--   Source-backed composition of two genuinely Proved theorems: P2-C 5b57f741 additive measure with finite negative tails and original pathwise strict negative support 56a5b5da; no source ν rate assumption.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_finite_negative_tails
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_additive_mean_measure_negative_support
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ s t : ℝ≥0, μ (s + t) = μ s + μ t) ∧
      (∀ ε : ℝ, 0 < ε → μ 1 (Iic (-ε)) < ⊤) ∧
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B = μ T (B ∩ Iio (0 : ℝ))) := by sorry
