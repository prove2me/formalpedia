-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:24:43.576399+00:00
-- url     : https://prove2.me/theorems/7c95a8cd-65b4-4587-a80c-3b3e07078c99
-- title:
--   The same source intrinsic mark-count measure has time additivity, negative support, finite tails and sigma-finiteness
-- statement:
--   There is one and the same original-process expected marked-count measure family with source representation, time additivity, finite negative tails, strict negative support and sigma-finiteness at every horizon. The two established existential witnesses agree by measure extensionality on measurable Borel mark sets. No prescribed ν-rate equality is assumed.
-- source:
--   Proved P2-C source additive negative-support measure theorem 4d799f07 and Proved all-horizons sigma-finiteness theorem 1bb36998, combined through exact source representation and Measure.ext.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_negative_support
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_expected_measure_sigma_finite_additive_package
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
        μ T B = μ T (B ∩ Iio (0 : ℝ))) ∧
      (∀ T : ℝ≥0, SigmaFinite (μ T)) := by sorry
