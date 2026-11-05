-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests
-- name    : AvramDividend.Classical.avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:47:29.073595+00:00
-- url     : https://prove2.me/theorems/db86ddc9-264b-4c2a-b0dc-21e2c4bc3bb4
-- title:
--   Original signed compact-negative tests identify the same intrinsic mark intensity as the genuine Lévy measure
-- statement:
--   For the actual source Lévy X under the probability measure, build one all-horizon original intrinsic mark intensity σ and prove equality of its real Bochner integrals and original X.ν integrals for every signed continuous compactly supported negative-mark test. Use the accepted original nonnegative moment identity, known separated-band finiteness and signed Jordan conversion.

import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_assist_original_positive_compact_intensity_eq_nu_tests_v3
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_signed_compact_test_eq_of_positive_lintegrals
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_integrable_of_locally_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_a_assist_original_signed_compact_intensity_eq_nu_tests
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ σ : Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ B) ∂P) = (T : ℝ≥0∞) * σ B) ∧
      (∀ (f : ℝ → ℝ), Continuous f → IsCompact (tsupport f) →
        tsupport f ⊆ Iio (0 : ℝ) →
        (∫ y, f y ∂σ) =
          (∫ y, f y ∂(X.ν.restrict (Iio (0 : ℝ))))) ∧
      (∀ ε : ℝ, 0 < ε → σ (Iic (-ε)) < ⊤) ∧
      (∀ B : Set ℝ, MeasurableSet B →
        σ B = σ (B ∩ Iio (0 : ℝ))) ∧
      SigmaFinite σ := by sorry
