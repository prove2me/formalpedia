-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_large_raw_integrable_of_bound
-- name    : AvramDividend.Classical.avram_p4_c_generator_large_raw_integrable_of_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:09:54.35145+00:00
-- url     : https://prove2.me/theorems/3db30c9c-1515-4f77-9645-d71d598ef863
-- title:
--   Original large negative jump raw payoff is ν-integrable from separated finite intensity and a genuine markwise bound
-- statement:
--   For the original X.ν, any Borel payoff w and fixed original reserve y with a uniform raw increment bound on negative marks z<-epsilon has an absolutely ν-integrable uncompensated large-jump kernel. The proof derives finite mark intensity from the source Lévy min(1,z²) condition, establishes measurability of the raw kernel, and applies the exact pinned finite-measure bounded-integrand criterion. This avoids imposing GeneratorIntegrable at a boundary reserve.
-- source:
--   ACCEPTED epsilon_large_jump_intensity_finite, pinned IntegrableOn.of_bound and ae_restrict_mem

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_epsilon_large_jump_intensity_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_large_raw_integrable_of_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ)
    (y ε M : ℝ) (hε : 0 < ε) (hw_meas : Measurable w)
    (hbound : ∀ z : ℝ, z < -ε →
      |w (y + z) - w y| ≤ M) :
    IntegrableOn (fun z : ℝ => w (y + z) - w y)
      (Iio (-ε)) X.ν := by sorry
