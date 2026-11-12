-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB70_uniform_two_grid_weighted_block_regroup
-- name    : AvramDividend.Classical.avram_gbB70_uniform_two_grid_weighted_block_regroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:08:13.556019+00:00
-- url     : https://prove2.me/theorems/f3389bb7-21cf-4c7c-bbeb-2df110653a13
-- title:
--   Finite weighted block regrouping under uniform common refinement
-- statement:
--   An elementary finite-sum block regrouping identity: group a fine grid of (m+1)(p+1) cells into m+1 consecutive blocks of p+1 cells. Within each block the coarse coefficient is g(i), equivalently g(r/(p+1)) on the flattened index.
-- source:
--   Original Gaussian B deterministic common-refinement arithmetic, 11 November 2026.

import Mathlib
open scoped BigOperators

theorem AvramDividend.Classical.avram_gbB70_uniform_two_grid_weighted_block_regroup
    (m p : ℕ) (f g : ℕ → ℝ) :
    (Finset.range (m + 1)).sum (fun i =>
      g i * (Finset.range (p + 1)).sum (fun j =>
        f (i * (p + 1) + j))) =
    (Finset.range ((m + 1) * (p + 1))).sum (fun r =>
      g (r / (p + 1)) * f r) := by sorry
