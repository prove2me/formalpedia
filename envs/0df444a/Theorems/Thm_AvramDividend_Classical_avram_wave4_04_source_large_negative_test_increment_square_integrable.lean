-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_large_negative_test_increment_square_integrable
-- name    : AvramDividend.Classical.avram_wave4_04_source_large_negative_test_increment_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T17:16:07.440015+00:00
-- url     : https://prove2.me/theorems/e069518d-9097-40bd-8803-f6f587260d35
-- title:
--   Original source Lévy large negative test-function jumps have finite quadratic variation without a first-moment assumption
-- statement:
--   For the actual source Lévy measure ν, any verification candidate continuous on nonnegative reserves and identically zero on negative reserves has square-integrable large negative test-function increments at any nonnegative reserve y where the original GeneratorIntegrable premise holds. This uses only finite ν mass away from zero and boundedness of w over the compact segment from 0 to y, even when arbitrarily large negative jumps have infinite first absolute moment. The result establishes the large-mark L² integrability prerequisite for original-filtration compensated-jump localisation; it does not assume an unrelated Poisson representation or assert a martingale/Itô–Meyer formula.
-- source:
--   Avram–Palmowski–Pistorius (2007) Proposition 4(i), original source X and generator. Proven canonical helpers levy_negative_mass_away_from_zero_finite UUID 0ff609aa-898f-40d5-b3d2-1875be4f2fea and generatorIntegrand_large_negative_integrable UUID d6d42ac6-8d73-463d-9224-0d3191ad7a0a. Exact 62-line source remotely elaborated to intentional sentinel at job 8150a135-1349-4f23-bbb7-414095897065, candidate error lines empty. Supports (but does not solve) corrected original-X adapted-D UBV stochastic core UUID 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_source_large_negative_test_increment_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (y : ℝ) (hy : 0 ≤ y)
    (hGen : X.GeneratorIntegrable w y) :
    IntegrableOn (fun z : ℝ => (w (y + z) - w y) ^ 2)
      (Iic (-1 : ℝ)) X.ν := by sorry
