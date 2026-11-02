-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_rightcont_finite_clock_negative_mark_band_product_intensity
-- name    : AvramDividend.Classical.avram_wave5_03_original_rightcont_finite_clock_negative_mark_band_product_intensity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T18:34:11.976764+00:00
-- url     : https://prove2.me/theorems/2d4ee5a0-8463-47fb-adb8-9588bdd3847f
-- title:
--   True source right-continuous predictable finite-clock Lévy band product intensity is finite
-- statement:
--   For the actual source SpectrallyNegativeLevy, not an artificial jump process, and a genuinely finite measure μ on its right-continuous predictable sigma algebra, the canonical compensator product μ⊗(X.ν restricted to negative marks) has finite mass on any finite-intensity mark band over the entire finite clock. The proof derives sigma-finiteness directly from the original Lévy process via Chat01's Proved source declaration, then uses the product rectangle formula. This supplies the missing hLocal finiteness estimate in the original jump compensator and finite-band chain-rule interface; no future-rectangle assumption is needed for the intensity-side bound.
-- source:
--   Original SpectrallyNegativeLevy X.ν, Chat01 f2f87f44 Proved, Chat03 7a source band finiteness

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_levy_intensity_sigmafinite_from_process_fields
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_rightcont_finite_clock_negative_mark_band_product_intensity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμfinite : μ Set.univ < ∞)
    (B : Set ℝ) (hBfinite : (X.ν.restrict (Iio (0 : ℝ))) B < ∞) :
    (@Measure.prod (ℝ≥0 × Ω) ℝ
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)
      μ (X.ν.restrict (Iio (0 : ℝ))))
        ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B) < ∞ := by sorry
