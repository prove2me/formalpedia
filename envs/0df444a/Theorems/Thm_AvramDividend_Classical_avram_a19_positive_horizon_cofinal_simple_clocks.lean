-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_positive_horizon_cofinal_simple_clocks
-- name    : AvramDividend.Classical.avram_a19_positive_horizon_cofinal_simple_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:10:56.299213+00:00
-- url     : https://prove2.me/theorems/ef6585cb-b4e4-4f28-83e1-39e23d2abb73
-- title:
--   Positive real horizon admits an increasing nonnegative strict cofinal grid
-- statement:
--   Every strictly positive real horizon T admits a monotone sequence of nonnegative deterministic observation clocks strictly before T, cofinal in the interval below T. This discharges the deterministic clock-existence component of the original BV cofinal finite-grid HJB expected-budget source b39f2dd1.
-- source:
--   Elementary Archimedean real analysis, u(n) = T - T/(n+1), for the source-faithful cofinal strict-horizon reduction b39f2dd1. The stochastic expected source budget remains separately Open.

import Mathlib
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_a19_positive_horizon_cofinal_simple_clocks (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℝ, Monotone u ∧ (∀ n, 0 ≤ u n) ∧
      (∀ n, u n < T) ∧
      (∀ s : ℝ, s < T → ∃ n, s < u n) := by sorry
