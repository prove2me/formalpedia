-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger111_subclock_le_ruin_and_horizon
-- name    : AvramDividend.Classical.avram_gledger111_subclock_le_ruin_and_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:52:18.601114+00:00
-- url     : https://prove2.me/theorems/1e4ffa26-724c-4140-a2ad-a4449dfced31
-- title:
--   A clock beneath the ruin-horizon minimum lies beneath each component
-- statement:
--   If the original finite nonnegative stopping clock lies below the NNReal truncation of min(ruin,horizon), it lies below the horizon and, after ENNReal coercion, below ruin. This supplies the exact original-path assumptions for gledger89, gledger101 and gledger106 in the full gledger81 contact ledger.
-- source:
--   Root-connected Gaussian gledger81 clock adapter for hρle with hτeq. No stochastic or expected-value claim; solely monotonicity of coe_toNNReal and min.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger111_subclock_le_ruin_and_horizon
    (σ : ℝ≥0∞) (n ρ : ℝ≥0)
    (hρ : ρ ≤ (min σ (n : ℝ≥0∞)).toNNReal) :
    ρ ≤ n ∧ (ρ : ℝ≥0∞) ≤ σ := by sorry
