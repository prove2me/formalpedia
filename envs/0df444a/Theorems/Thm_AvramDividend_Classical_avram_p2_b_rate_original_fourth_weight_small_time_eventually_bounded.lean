-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
-- name    : AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:26:42.802163+00:00
-- url     : https://prove2.me/theorems/c60447dc-42e4-40ec-90c4-fb413f320b3c
-- title:
--   Original Lévy fourth-weight small-time ratio is eventually bounded
-- statement:
--   For the actual original spectrally negative Lévy process and nonnegative theta, the source fourth-exponential derivative theorem implies that in a punctured right neighbourhood of h=0 the ratio of E[(exp(theta X_h)-1)^4] to h is strictly below its original negative Lévy measure limit plus one. This provides a concrete source-specific eventual O(h) control, from the proven exponential derivative and a genuine neighbourhood bound, without assuming any jump intensity identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_source_fourth_weighted_exponential_small_time_derivative
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_b_rate_original_fourth_weight_small_time_eventually_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ((∫ ω, (Real.exp (θ * X.X (Real.toNNReal h) ω) - 1) ^ 4 ∂P) / h) <
        (∫ y in Iio (0 : ℝ), (Real.exp (θ * y) - 1) ^ 4 ∂X.ν) + 1 := by sorry
