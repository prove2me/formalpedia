-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c
-- name    : AvramDividend.Classical.bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:53:56.367885+00:00
-- url     : https://prove2.me/theorems/f083f54c-36f8-43ab-b87e-1ca6bbbd0206
-- title:
--   Capped extended-nonnegative right grid limits transfer to finite nonnegative clocks
-- statement:
--   For a finite cap of an ENNReal raw clock, convergence of grid clocks from above in ENNReal implies convergence of their NNReal values to the true finite capped clock, with the same one-sided bound. This preserves the exact original mathematical statement.
-- source:
--   Causal authoring repair of terminal failed job 694a98a9-9173-4ddc-a341-c67881e97f56. Unknown namespace AvramDividend.Classical aborted the open command and left Tendsto unresolved; the corrected statement preamble opens only imported namespaces. Proof source is work/avram_ws01c_capped_grid_enn_to_nn_solution_repair_20261028.lean.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.ENNReal.Real

open Filter Topology
open scoped ENNReal NNReal

theorem AvramDividend.Classical.bv_capped_grid_ENNReal_toNNReal_right_limit_ws01c
    {Ω : Type*}
    (grid : ℕ → Ω → ℝ≥0) (raw : Ω → ℝ≥0∞)
    (T : ℝ≥0)
    (hEnn : ∀ ω : Ω, Tendsto
      (fun n : ℕ => (grid n ω : ℝ≥0∞)) atTop
      (𝓝 (raw ω ⊓ (T : ℝ≥0∞))))
    (hAbove : ∀ (ω : Ω) (n : ℕ),
      raw ω ⊓ (T : ℝ≥0∞) ≤ (grid n ω : ℝ≥0∞)) :
    (∀ ω : Ω, Tendsto (fun n : ℕ => grid n ω) atTop
      (𝓝 ((raw ω ⊓ (T : ℝ≥0∞)).toNNReal))) ∧
    (∀ (ω : Ω) (n : ℕ),
      (raw ω ⊓ (T : ℝ≥0∞)).toNNReal ≤ grid n ω) := by sorry
