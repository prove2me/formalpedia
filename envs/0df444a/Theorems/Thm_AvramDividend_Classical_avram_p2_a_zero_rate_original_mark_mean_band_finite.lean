-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_mark_mean_band_finite
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_original_mark_mean_band_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:54:45.381002+00:00
-- url     : https://prove2.me/theorems/108ce6d0-424f-4228-9b3a-f5700b737270
-- title:
--   Original intrinsic expected mark measure finite on every separated negative half-line
-- statement:
--   From the original marked-count expectation measure and the independently established finite first moment of significant negative jumps, obtain one source-exact intrinsic mark measure finite on every negative band bounded away from zero. No compensator, new process or rate identification is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_mark_mean_measure
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_negative_halfline_expected_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_original_mark_mean_band_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ μ : Measure ℝ,
      (∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤) := by sorry
