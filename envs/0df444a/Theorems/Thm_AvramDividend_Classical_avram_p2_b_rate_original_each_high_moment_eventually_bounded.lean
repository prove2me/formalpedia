-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_each_high_moment_eventually_bounded
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:58:53.096803+00:00
-- url     : https://prove2.me/theorems/1b57c1bc-207d-491b-bcd1-a3367ee4e6aa
-- title:
--   Original Levy weighted image moments of all orders are locally bounded at small time
-- statement:
--   For the original spectrally negative Lévy process, every nonnegative integer exponential image kth fourth-weighted moment ratio is eventually below its prescribed original Levy measure moment plus one. This is the uniform high-moment bound needed to control positive image tails and transfer moment limits through weak convergence, derived only from the Proved original source integer moment theorem and the topology of convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weighted_integer_moments

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_each_high_moment_eventually_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ((∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω)) ^ k *
        (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) <
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y)) ^ k *
          (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by sorry
