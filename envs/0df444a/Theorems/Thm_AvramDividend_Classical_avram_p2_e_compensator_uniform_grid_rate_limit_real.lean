-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_rate_limit_real
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_rate_limit_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:55:21.592096+00:00
-- url     : https://prove2.me/theorems/ce58ba1a-f029-4dcb-89a9-ebebeb0556be
-- title:
--   Real uniform-grid second-factorial rate factor converges to the one-half limit
-- statement:
--   For any real time horizon and negative-band Lévy rate, the triangular uniform grid rate factor (Tλ)²k/[2(k+1)] converges to (Tλ)²/2.
-- source:
--   Pinned tendsto_one_div_add_atTop_nhds_zero_nat; deterministic rate-limit companion to the original source finite-grid mean and Fatou passage.

import Mathlib

open Filter Topology

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_rate_limit_real (T rate : ℝ) :
    Filter.Tendsto
      (fun k : ℕ => ((T * rate) ^ 2 / 2) *
        ((k : ℝ) / ((k : ℝ) + 1))) Filter.atTop
      (𝓝 ((T * rate) ^ 2 / 2)) := by sorry
