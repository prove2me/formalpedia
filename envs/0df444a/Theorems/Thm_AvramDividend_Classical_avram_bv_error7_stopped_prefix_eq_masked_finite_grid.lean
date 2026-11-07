-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_stopped_prefix_eq_masked_finite_grid
-- name    : AvramDividend.Classical.avram_bv_error7_stopped_prefix_eq_masked_finite_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:57:15.553863+00:00
-- url     : https://prove2.me/theorems/d1e28a2b-2c63-4cf6-9dee-a91e69107098
-- title:
--   Random stopped-grid finite prefix equals masked physical-grid envelope
-- statement:
--   On a fixed physical grid of N finite cells, a sample-dependent prefix of length k≤N is exactly the full physical-grid envelope whose cells i≥k have been masked to zero. This pathwise identity is used with the original BV C1 source and makes the final contact cell explicit.
-- source:
--   Source-exact stopped prefix/remainder reconciliation supporting original-process measurability.

import Mathlib
open MeasureTheory Set Filter
open scoped BigOperators

theorem AvramDividend.Classical.avram_bv_error7_stopped_prefix_eq_masked_finite_grid (N k : ℕ) (hk : k ≤ N) (f : ℕ → ℝ) :
    (∑ i ∈ Finset.range N, if i < k then f i else 0) =
      ∑ i ∈ Finset.range k, f i := by sorry
