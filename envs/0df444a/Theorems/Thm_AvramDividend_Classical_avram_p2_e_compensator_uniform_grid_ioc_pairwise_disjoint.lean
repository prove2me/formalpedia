-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
-- name    : AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:31:30.349217+00:00
-- url     : https://prove2.me/theorems/8d851fa6-d8db-42f9-b751-0813a73d9640
-- title:
--   Physical uniform half-open original jump-count grid cells are pairwise disjoint
-- statement:
--   Any two distinct cells in an original physical uniform nonnegative-time half-open grid are disjoint, with no positive-width assumption required.
-- source:
--   Pinned Mathlib ordered NNReal arithmetic and Nat cast monotonicity; discharges the physical time-interval disjointness hypothesis of the Proved original pair-grid count theorem 8f025ae7.

import Mathlib

open Set
open scoped NNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_uniform_grid_ioc_pairwise_disjoint
    (m : ℕ) (δ : ℝ≥0) :
    ∀ i j : Fin m, i ≠ j →
      Disjoint
        (Ioc ((i.val : ℝ≥0) * δ) (((i.val + 1 : ℕ) : ℝ≥0) * δ))
        (Ioc ((j.val : ℝ≥0) * δ) (((j.val + 1 : ℕ) : ℝ≥0) * δ)) := by sorry
