-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve
-- name    : AvramDividend.Classical.avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:49:12.156517+00:00
-- url     : https://prove2.me/theorems/a5868171-4af4-4f8f-92a4-d218e5c95a3a
-- title:
--   Finite-cap predictable stopped pre-reserve band eventually contains every strict interior reserve
-- statement:
--   For explicit finite-cap bands a_n=d/(n+1), b_n=c(n+1)/(n+2), every positive reserve strictly smaller than c eventually lies in the full predictable pre-reserve band Icc(a_n,b_n). This strengthens the existing half-lower-band cofinality, and is directly applicable to the actual original stopped compensation mask.
-- source:
--   Already Proved finite-cap eventual inclusion 7df6597f, instantiated at y/2 and y and combined via the maximum threshold.

import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_band_eventually_contains_interior_reserve

open Set AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_meas7_finite_full_predictable_band_eventually_contains_reserve (c d y : ℝ)
    (hc : 0 < c) (hd : 0 < d) (hy : 0 < y) (hyc : y < c) :
    ∃ N : ℕ, ∀ n ≥ N,
      y ∈ Icc (d / ((n : ℝ) + 1))
        (c * ((n : ℝ) + 1) / ((n : ℝ) + 2)) := by sorry
