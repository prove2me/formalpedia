-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_uniform_source_grid_endpoints
-- name    : AvramDividend.Classical.avram_leanlevy_bridge_uniform_source_grid_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T17:27:50.276709+00:00
-- url     : https://prove2.me/theorems/6bdc2c26-838f-4e38-ad2f-31ff5818997b
-- title:
--   Exact NNReal original physical uniform-cell endpoints satisfy the stochastic pair-count bridge hypotheses
-- statement:
--   For each positive integer grid size, the genuine NNReal physical intervals sᵢ=iT/k and tᵢ=(i+1)T/k have sᵢ≤tᵢ≤T and coerce to exactly the real endpoint formulas used by the original X ceiling-bin counts. This provides the concrete endpoint functions for applying the stopped-jump same-space compensator bridge without extra endpoint assumptions.
-- source:
--   Mathlib NNReal coercion, positivity and order, pinned 0df444a; no Lévy representation or equality-in-law transfer.

import Mathlib
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_leanlevy_bridge_uniform_source_grid_endpoints
    (T : ℝ≥0) (k : ℕ) (hk : 0 < k) :
    let s : Fin k → ℝ≥0 := fun i => ((i.val : ℝ≥0) * T) / (k : ℝ≥0)
    let t : Fin k → ℝ≥0 := fun i => (((i.val + 1 : ℕ) : ℝ≥0) * T) / (k : ℝ≥0)
    (∀ i, s i ≤ t i) ∧ (∀ i, t i ≤ T) ∧
    (∀ i, (s i : ℝ) = (i.val : ℝ) * (T : ℝ) / (k : ℝ)) ∧
    (∀ i, (t i : ℝ) = ((i.val + 1 : ℕ) : ℝ) * (T : ℝ) / (k : ℝ)) := by sorry
