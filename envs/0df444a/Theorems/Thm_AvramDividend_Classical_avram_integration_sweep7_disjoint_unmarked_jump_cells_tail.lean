-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
-- name    : AvramDividend.Classical.avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:22:44.415946+00:00
-- url     : https://prove2.me/theorems/a333aff8-f975-497b-bd23-538e9c6be129
-- title:
--   Disjoint unmarked original jump-grid cell mass is bounded by excluded jump-series tail
-- statement:
--   For any absolutely summable nonnegative jump weights, a finite collection of disjoint source grid cells that avoid a chosen finite set of marked jumps has total jump mass at most the sum of the unmarked weights. The unique-cell premise corresponds exactly to the half-open (u_i,u_{i+1}] original jump-time convention. The theorem requires no stochastic law, and does not assume a mesh limit.
-- source:
--   Needed P3-F mesh-junction estimate: combine source finite negative jump-time exclusion 0b53d65a-d9f5-4f84-b2da-e234b6b93864 and positive marked jump-removed cell vanishing (published P3-F) with this independent Tonelli/finite-disjoint-support bound. The original full-measure sample path supplies j(t)=leftLim X.X(t)-X.X(t)≥0, Summable j, the interval-cell uniqueness and avoidance. Exact pinned names Summable.of_norm_bounded, Summable.tsum_finsetSum and Summable.tsum_le_tsum are available; no original-source stochastic statement is assumed or weakened.

import Mathlib
open Filter Set
open scoped BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_integration_sweep7_disjoint_unmarked_jump_cells_tail
    {ι : Type*} (j : ι → ℝ)
    (hj : Summable j) (hjnonneg : ∀ t, 0 ≤ j t)
    (marked : Finset ι) (cells : Finset ℕ)
    (inside : ℕ → ι → Prop)
    (hUnique : ∀ t i, i ∈ cells → ∀ k, k ∈ cells →
      inside i t → inside k t → i = k)
    (hAvoid : ∀ i, i ∈ cells → ∀ t, t ∈ marked → ¬ inside i t) :
    (∑ i ∈ cells, ∑' t, if inside i t then j t else 0) ≤
      ∑' t, if t ∈ marked then 0 else j t := by sorry
