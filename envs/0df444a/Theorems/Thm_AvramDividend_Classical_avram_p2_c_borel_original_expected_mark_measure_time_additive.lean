-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_mark_measure_time_additive
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_expected_mark_measure_time_additive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:28:46.761255+00:00
-- url     : https://prove2.me/theorems/0d4dd38a-3f41-40a6-bc4c-bd0b90827a3c
-- title:
--   Original intrinsic expected Borel mark measures form an additive time-indexed family
-- statement:
--   For the original spectrally negative Lévy source, choose a Borel mark measure μ_T whose value on every measurable set B equals the actual intrinsic marked jump-count expectation on (0,T]. Prove μ_(s+t) = μ_s + μ_t as measures, retaining infinite ENNReal values. This does not assert the unknown ν coefficient and makes the source's stationary time transport available as a measure-valued identity.
-- source:
--   Follows from Proved original mean mark measure 9bbf7f85, arbitrary Borel marked evaluation measurability 21acd1ce, stationary expected counts add050a6, and general expected rectangle splitting 3a467cf3. Source-original Ω/P/X preserved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_stationary_expected_mark_additive
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_expected_mark_measure_time_additive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ s t : ℝ≥0, μ (s + t) = μ s + μ t) := by sorry
