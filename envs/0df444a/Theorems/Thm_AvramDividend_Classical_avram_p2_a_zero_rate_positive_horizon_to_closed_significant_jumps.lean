-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:03:24.144681+00:00
-- url     : https://prove2.me/theorems/09b985a7-7326-4c74-b536-d7619c689198
-- title:
--   Positive-time original jump support extends to closed horizon with zero-time no-jump
-- statement:
--   An original càdlàg source path with left limit equal to its value at time zero has no significant jump at the origin for positive cutoff rho. Therefore any finite jump-time set covering all significant positive-time jumps up to T also covers significant marks on the closed interval [0,T]. This discharges the zero-time boundary difference in the accepted full-grid pathwise theorem without inserting a spurious zero-time atom.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_full_grid_compact_test_jump_limit
open Filter Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_a_zero_rate_positive_horizon_to_closed_significant_jumps
    (Y : ℝ≥0 → ℝ) (T : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hzero : Y 0 = Function.leftLim Y 0)
    (F : Finset ℝ≥0)
    (hF : ∀ t ∈ Ioc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F) :
    ∀ t ∈ Icc (0 : ℝ≥0) T,
      ρ ≤ |Y t - Function.leftLim Y t| → t ∈ F := by sorry
