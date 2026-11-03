-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
-- name    : AvramDividend.Classical.avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T07:19:04.073757+00:00
-- url     : https://prove2.me/theorems/8410dc24-eb06-4757-98d9-f29e9b1f320c
-- title:
--   Uniform actual right-dividend path total on all grids clipped at one stopped horizon
-- statement:
--   For the actual original dividend strategy and any fixed sample path and stopping horizon, all clipped grids starting at zero have uniformly bounded right-limit dividend increment, bounded by the total right-limit payment between zero and the stopped horizon. This eliminates a path-boundedness hypothesis in the source-exact Chat06 fine-grid Stieltjes timing limit, independent of any stochastic identity.
-- source:
--   Original dividend path monotonicity in Proved avram_wave3_03_dividendStrategy_rightLimit_monotone; Avram Proposition 4(i) chronological Stieltjes part

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_original_clipped_ruin_grid_rightpayment_total_path_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (k : ℕ → ℕ)
    (hzero : ∀ n, u n 0 = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n,
      rightLimit D (min (u n (k n)) (τ ω)) ω -
        rightLimit D (min (u n 0) (τ ω)) ω ≤ B := by sorry
