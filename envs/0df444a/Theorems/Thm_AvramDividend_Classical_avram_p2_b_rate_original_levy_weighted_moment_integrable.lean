-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_levy_weighted_moment_integrable
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T19:41:38.357105+00:00
-- url     : https://prove2.me/theorems/6019c332-89da-4b3e-9258-419ae09b58c0
-- title:
--   Original Lévy measure has integrable shifted fourth exponential jump kernel
-- statement:
--   For the genuine source Lévy measure X.ν, every nonnegative shift rho and nonnegative slope theta gives Bochner integrability of exp(rho*y)*(exp(theta*y)-1)^4 over negative jump marks. The proof combines five source generator integrable kernels from the proved levyWeight_integrable and levy_exponential_generatorIntegrable_of_moment facts; it does not use or assume a jump rate. This is the missing actual ν-integrability prerequisite for P2-B moment domination and no-positive-increment tail inversion.

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_exp_mul

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_levy_weighted_moment_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ρ θ : ℝ) (hρ : 0 ≤ ρ) (hθ : 0 ≤ θ) :
    IntegrableOn
      (fun y : ℝ => Real.exp (ρ * y) *
        (Real.exp (θ * y) - 1) ^ 4) (Iio (0 : ℝ)) X.ν := by sorry
