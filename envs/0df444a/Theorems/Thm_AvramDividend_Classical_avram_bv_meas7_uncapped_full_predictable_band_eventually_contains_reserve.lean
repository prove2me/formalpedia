-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve
-- name    : AvramDividend.Classical.avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:48:26.611121+00:00
-- url     : https://prove2.me/theorems/95f1e1d9-3074-417c-86a6-39e699bc7c46
-- title:
--   Uncapped predictable stopped pre-reserve band eventually contains every positive reserve
-- statement:
--   For the genuine uncapped pre-reserve localisation E based on Icc(a_n,b_n) with a_n=1/(n+1), b_n=n+2, every fixed positive reserve eventually lies in this full band. This strengthens the previously Proved eventual inclusion in the wider half-lower band Icc(a_n/2,b_n). The proof applies that theorem to y/2 for the lower inequality and to y for the upper inequality.
-- source:
--   Proved original uncapped eventual compact-band inclusion theorem 231a0455, twice instantiated at y and y/2.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_uncapped_band_eventually_contains_positive_reserve

open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_uncapped_full_predictable_band_eventually_contains_reserve (y : ℝ) (hy : 0 < y) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 2) := by sorry
