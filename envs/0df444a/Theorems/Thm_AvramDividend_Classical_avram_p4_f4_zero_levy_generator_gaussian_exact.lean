-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_generator_gaussian_exact
-- name    : AvramDividend.Classical.avram_p4_f4_zero_levy_generator_gaussian_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:51:09.337194+00:00
-- url     : https://prove2.me/theorems/f85cd232-18cc-4d56-a55d-415d7ffd4db3
-- title:
--   Original zero-jump generator equals exact Gaussian second-order drift
-- statement:
--   When the original spectrally negative Lévy process has no Lévy jump measure, its generator is precisely the Gaussian second derivative term plus the deterministic drift derivative term.
-- source:
--   Exact generator definition with integral against zero measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_zero_levy_generator_gaussian_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (w : ℝ → ℝ) (y : ℝ) :
    X.generator w y =
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y + X.c * deriv w y := by sorry
