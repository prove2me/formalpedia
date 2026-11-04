-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_automatic_uniform_physical_negative_levy_integral
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_C1_automatic_uniform_physical_negative_levy_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:50:06.263207+00:00
-- url     : https://prove2.me/theorems/ee77d3ae-427b-45e2-a383-a64d5af3ddd3
-- title:
--   Automatic original BV C1 uniform physical negative Lévy generator integral
-- statement:
--   Under the unchanged original BV positive-cap C1 candidate assumptions, the full original negative-jump ν-integral has one finite uniform absolute bound on every compact interior reserve strip. Measurability, Lipschitz slope, ruin-overshoot value bound and finite distant-mark mass are all derived rather than postulated.
-- source:
--   Accepted source value measurability 4adbe17d, automatic compact negative ν majorant data and original uniform negative-jump integral bound 7fc76e56.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_value_measurable_of_positive_continuity
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_candidate_one_sided_value_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_negative_levy_tail_finite_at_BV_C1_threshold
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_uniform_physical_negative_levy_integral_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_C1_automatic_uniform_physical_negative_levy_integral
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (C : ℝ≥0∞) (w : ℝ → ℝ)
  (hwCont : ContinuousOn w (Ici 0))
  (hwNeg : ∀ v : ℝ, v < 0 → w v = 0)
  (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
  (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hBand : Icc (a / 2) b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
  ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Icc a b,
    |∫ z in Iio (0 : ℝ), w (y + z) - w y ∂X.ν| ≤ M := by sorry
