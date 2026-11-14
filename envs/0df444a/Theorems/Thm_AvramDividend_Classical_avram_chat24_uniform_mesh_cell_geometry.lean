-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_mesh_cell_geometry
-- name    : AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T21:35:51.8552+00:00
-- url     : https://prove2.me/theorems/7c1f5504-b3c9-4539-9b5e-8224817404e5
-- title:
--   Strict monotonicity, width and endpoints of the uniform positive mesh
-- statement:
--   Elementary geometry of B*i/(n+1) for positive B: strict monotonicity, positive mesh width, and band endpoint bounds and exact real width for all cells in range(n+1). Supplies the common geometric premises of both drift and jump branches in parent 7b52eba8-6fe9-40c9-89f7-a341ca70210b. A full direct proof is preserved in p2m-drift-mesh-geometry-research.lean. It imports no platform theorem and creates no dependency cycle.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_chat24_uniform_mesh_cell_geometry
    (B : ℝ≥0) (hB : 0 < B) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i => B * (i : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let h : ℕ → ℝ := fun n => (B : ℝ) / ((n + 1 : ℕ) : ℝ)
    (∀ n, StrictMono (u n)) ∧ (∀ n, 0 < h n) ∧
      (∀ n i, i ∈ Finset.range (n + 1) →
        u n i ≤ B ∧ u n (i + 1) ≤ B ∧ (u n (i + 1) : ℝ) - (u n i : ℝ) = h n) := by sorry
