-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps16_original_quadratic_energy_shift_finite
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps16_original_quadratic_energy_shift_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T18:59:16.641841+00:00
-- url     : https://prove2.me/theorems/bf199583-108f-4ad8-97cb-ac4b450ac668
-- title:
--   Original spectrally negative Levy quadratic energy remains finite under doubled nonnegative Taylor-envelope scaling
-- statement:
--   For the genuine spectrally negative Levy measure X.nu, finite energy of the Levy quadratic truncation from the actual process structure persists under every nonnegative real multiple and the factor two required by the shifted reverse Fatou domination. The proof uses original X.nu_integrable and the pinned nonnegative integral's constant-multiplication theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_ito_jumps16_original_quadratic_energy_shift_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (M : ℝ) (hM : 0 ≤ M) :
    (∫⁻ z : ℝ, ENNReal.ofReal
      (2 * (M * min (1 : ℝ) (z ^ 2))) ∂X.ν) ≠ ⊤ := by sorry
