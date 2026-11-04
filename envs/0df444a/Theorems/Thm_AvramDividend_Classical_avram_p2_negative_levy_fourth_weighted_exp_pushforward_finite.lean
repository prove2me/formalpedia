-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
-- name    : AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:17:39.341473+00:00
-- url     : https://prove2.me/theorems/925a9151-2aa8-4af8-b10c-49aec025fd2c
-- title:
--   Negative source Lévy fourth-weighted exponential image is a finite measure
-- statement:
--   The original Lévy measure restricted to negative marks, weighted by the nonnegative fourth exponential deficit, and pushed forward under exp defines a genuinely finite measure. Proof constructs the fourth finite-difference combination of integrable compensated exponentials from source generator integrability, so the weighting has finite source mass. This gives the candidate limit measure in the weighted method-of-moments argument without a Poisson copy or postulated jump intensity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_fourth_weighted_exp_pushforward_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    IsFiniteMeasure
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map Real.exp) := by sorry
