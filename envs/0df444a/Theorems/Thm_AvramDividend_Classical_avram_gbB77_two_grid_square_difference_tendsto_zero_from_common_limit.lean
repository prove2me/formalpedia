-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB77_two_grid_square_difference_tendsto_zero_from_common_limit
-- name    : AvramDividend.Classical.avram_gbB77_two_grid_square_difference_tendsto_zero_from_common_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:02:11.600299+00:00
-- url     : https://prove2.me/theorems/2207fc5c-0ba4-4b61-8d18-eb784aed71b9
-- title:
--   Two arbitrary index sequences approaching a common limit have vanishing squared difference
-- statement:
--   The deterministic two-index convergence step for the original postpayment mesh: if the one-grid coefficient along increasing indices tends to a common finite real limit, then the squared difference at two independent grid indices tends to zero along the product atTop filter. The proof uses no Brownian replacement and is applied pathwise before stochastic domination in B61.

import Mathlib
open Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB77_two_grid_square_difference_tendsto_zero_from_common_limit
    (f : ℕ → ℝ) (a : ℝ) (hf : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun nm : ℕ × ℕ => (f nm.1 - f nm.2) ^ 2)
      atTop (𝓝 (0 : ℝ)) := by sorry
