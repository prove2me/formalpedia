-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a26_monotone_halfopen_grid_interval_partition_20261116
-- name    : AvramDividend.Classical.avram_a26_monotone_halfopen_grid_interval_partition_20261116
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T08:17:10.277135+00:00
-- url     : https://prove2.me/theorems/da209dde-1f71-448a-a0a9-4ae54c7a2e5f
-- title:
--   Any monotone finite time grid partitions its half-open horizon into adjacent cells
-- statement:
--   For every monotone original-time grid u indexed by natural numbers and each finite n, the union of its first n half-open cells (u_i,u_{i+1}] equals precisely (u_0,u_n]. Prove by finite induction, adjoining the last interval using Mathlib Set.Ioc_union_Ioc_eq_Ioc. This is the deterministic exact interval cover needed to count original physical jumps by their occupied equal-width cells.
-- source:
--   Pinned Mathlib Finset.set_biUnion_insert and Set.Ioc_union_Ioc_eq_Ioc. Original physical time grid preserves all endpoint conventions.

import Mathlib
open Set
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_a26_monotone_halfopen_grid_interval_partition_20261116
    (u : ℕ → ℝ≥0) (hmono : Monotone u) (n : ℕ) :
    (⋃ i ∈ Finset.range n, Set.Ioc (u i) (u (i + 1))) =
      Set.Ioc (u 0) (u n) := by sorry
