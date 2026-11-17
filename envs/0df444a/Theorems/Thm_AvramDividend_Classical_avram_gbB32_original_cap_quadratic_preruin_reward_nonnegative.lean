-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB32_original_cap_quadratic_preruin_reward_nonnegative
-- name    : AvramDividend.Classical.avram_gbB32_original_cap_quadratic_preruin_reward_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T18:56:37.846905+00:00
-- url     : https://prove2.me/theorems/47da7093-2098-43f8-8765-9fea8b4f76d0
-- title:
--   Original quadratic Gaussian candidate reward nonnegative strictly before ruin at cap one eighth
-- statement:
--   For the exact original barrier strategy starting at cap 1/8, show w(Y_t)≥0 for every strictly positive pre-ruin time, where w(y)=0 below zero and w(y)=2y−4y² otherwise. Use already kernel-Proved riskProcess pre-ruin nonnegativity and original barrier reserve cap bound. Discharges the precise hw_nonneg hypothesis in the selected positive-stop source for the concrete Gaussian candidate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_reserve_cap_bound_all_capital
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonnegative_strictly_before_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB32_original_cap_quadratic_preruin_reward_nonnegative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) <
        ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω →
      0 ≤ (fun z : ℝ => if z < 0 then 0 else 2 * z - 4 * z ^ 2)
        (riskProcess X (1 / 8 : ℝ)
          (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t ω) := by sorry
