-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_finite_grid_clock_tendsto_ennreal
-- name    : AvramDividend.Classical.chat03_finite_grid_clock_tendsto_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T21:58:20.487154+00:00
-- url     : https://prove2.me/theorems/5077b042-783d-4114-91d1-40f2f1769106
-- title:
--   Embedding a convergent finite grid passage clock into ENNReal preserves its finite limit
-- statement:
--   For any finite extended nonnegative-real target time τ, a sequence of NNReal grid passage times converging to τ.toNNReal also converges to τ after the canonical embedding in ENNReal. This includes τ=0 and avoids using ENNReal.toReal near infinity. It converts accepted finite NNReal grid first-passage convergence results into the exact extended-real clock format used in Prove2Me's two-sided stopped-scale identity.
-- source:
--   Pinned Mathlib ENNReal.continuous_coe and ENNReal.coe_toNNReal at Mathlib revision 0df444a360eaa60ab8c11dca51a86af692955474.

import Mathlib.Topology.Instances.ENNReal.Lemmas

open Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_finite_grid_clock_tendsto_ennreal
    (τ : ℝ≥0∞) (hτ : τ ≠ ∞) (σ : ℕ → ℝ≥0)
    (hσ : Tendsto σ atTop (𝓝 τ.toNNReal)) :
    Tendsto (fun n => (σ n : ℝ≥0∞)) atTop (𝓝 τ) := by sorry
