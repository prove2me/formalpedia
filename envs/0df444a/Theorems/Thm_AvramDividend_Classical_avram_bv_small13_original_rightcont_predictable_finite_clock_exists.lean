-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_small13_original_rightcont_predictable_finite_clock_exists
-- name    : AvramDividend.Classical.avram_bv_small13_original_rightcont_predictable_finite_clock_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T01:27:15.034775+00:00
-- url     : https://prove2.me/theorems/03b3da48-881b-493a-8344-f159927180ff
-- title:
--   Original physical right-continuous predictable stopped time clock witness without compact generator assumptions
-- statement:
--   For every original spectrally negative Levy source X and original dividend strategy D, a finite-horizon right-continuous predictable measure exists whose measurable sets agree exactly with the original physical time-by-probability product law. This source-exact witness is needed to instantiate the already Proved original predictable marked Campbell transfer at the true controlled zero-prestate event, in the infinite-negative-jump-activity bounded-variation localisation route. No global signed generator integrability, shifted strategy, auxiliary Levy process, or circular cap theorem is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_finite_horizon_predictable_intensity_budget

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_small13_original_rightcont_predictable_finite_clock_exists {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) : ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable), μ Set.univ < ⊤ ∧ ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A → μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A := by sorry
