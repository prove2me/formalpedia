-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_monotone_stopped_clock_prefix_selector
-- name    : AvramDividend.Classical.avram_route_runner_monotone_stopped_clock_prefix_selector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:27:04.61266+00:00
-- url     : https://prove2.me/theorems/204f43a5-a2c4-4b1f-807f-6f1aa82b427e
-- title:
--   Every monotone physical clock grid has a bounded stopped initial-segment selector
-- statement:
--   For each trajectory and finite monotone physical-time grid, select the first index where time is at least the stopping clock, or m if none. The stopped-grid cells are precisely the initial indices strictly below that bounded selector. This constructs the missing pointwise initial-segment mask needed before applying the Proved bounded predictable source prefix budget; adaptedness and measurability are separate subsequent obligations.
-- source:
--   Source exact stopped mask (u i : WithTop NNReal) < τ ω from avram_bv_env3_turn23; deterministic finite initial-segment construction required by Proved d046abd3 mask-to-bounded-prefix and Proved 2b993cd3 expected budget.

import Mathlib
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_monotone_stopped_clock_prefix_selector
    {Ω : Type*} (τ : Ω → WithTop ℝ≥0)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ) :
    ∃ k : Ω → ℕ,
      (∀ ω, k ω ≤ m) ∧
      (∀ ω i, i < m →
        ((u i : WithTop ℝ≥0) < τ ω ↔ i < k ω)) := by sorry
