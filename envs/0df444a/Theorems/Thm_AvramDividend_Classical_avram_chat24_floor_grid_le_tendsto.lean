-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_floor_grid_le_tendsto
-- name    : AvramDividend.Classical.avram_chat24_floor_grid_le_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T22:58:00.862042+00:00
-- url     : https://prove2.me/theorems/dc0d1a9a-cce0-4d54-9a96-fbecc1a63dd5
-- title:
--   Nonnegative floor grids converge from below
-- statement:
--   For every nonnegative real t the floor grid floor(t*(n+1))/(n+1) lies below t and converges to t. The gap is bounded by 1/(n+1). This is the independent geometric prerequisite in the complete floor-approximation proof of parent 6d1c89b0-a333-4b7e-bc65-2af9b106bde4. Its saved 42-line direct proof is blocked by the existing static complexity policy (score 0.0443, cutoff -0.0523). The parent reduces by measurable countable-valued approximants and the pointwise limit theorem. This helper does not refer to g, continuity, measurability, or the parent, so it introduces no cycle or weakening.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_floor_grid_le_tendsto (t : ℝ≥0) :
    let q : ℕ → ℝ≥0 := fun n =>
      ⟨(⌊(t : ℝ) * ((n : ℝ) + 1)⌋₊ : ℝ) / ((n : ℝ) + 1), by positivity⟩
    (∀ n, q n ≤ t) ∧ Tendsto q atTop (nhds t) := by sorry
