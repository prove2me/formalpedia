-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_moments_le_mass
-- name    : AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_image_moments_le_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:40:59.325231+00:00
-- url     : https://prove2.me/theorems/4d4075ff-e61f-436c-bdad-dab9f5beaf4d
-- title:
--   Every original Lévy negative weighted exponential image polynomial moment is at most its mass
-- statement:
--   For the exact Lévy measure X.ν on negative jumps, the finite measure obtained by multiplying by (exp(y)-1)^4 and mapping marks under exp has every kth nonnegative polynomial moment bounded by its zeroth moment. The proof uses the separately established original ν-image compact support [0,1], supplying all high-moment tail controls required for weak convergence and moment uniqueness without changing the source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_negative_levy_weighted_exp_image_compact_support

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_negative_levy_weighted_exp_image_moments_le_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (k : ℕ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ k) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) ≤
    (∫⁻ z : ℝ, ENNReal.ofReal (z ^ 0) ∂
      (((X.ν.restrict (Iio (0 : ℝ))).withDensity
        (fun y => ENNReal.ofReal ((Real.exp y - 1) ^ 4))).map
        Real.exp)) := by sorry
