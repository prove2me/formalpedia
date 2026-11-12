-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB94_finite_range_block_reindex
-- name    : AvramDividend.Classical.avram_gbB94_finite_range_block_reindex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:43:35.938475+00:00
-- url     : https://prove2.me/theorems/f5416ac2-b749-463d-beac-34350c7e30c5
-- title:
--   An M by b rectangular range sum equals the quotient-indexed flat range sum
-- statement:
--   Flattening a rectangle of M groups of b consecutive indices into a single length M*b natural range preserves every term. The coarse index for flat index r is its quotient r/b.
-- source:
--   Finite algebraic reindexing child of B91 coarse-step refinement.

import Mathlib
open scoped BigOperators

theorem AvramDividend.Classical.avram_gbB94_finite_range_block_reindex
    (M b : ℕ) (hb : 0 < b) (f : ℕ → ℕ → ℝ) :
    (Finset.range M).sum (fun i =>
      (Finset.range b).sum (fun j => f i (i * b + j))) =
    (Finset.range (M * b)).sum (fun r => f (r / b) r) := by sorry
