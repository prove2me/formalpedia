-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_positive_reciprocal_tail_cover
-- name    : AvramDividend.Classical.gaussian_positive_reciprocal_tail_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T18:11:20.345324+00:00
-- url     : https://prove2.me/theorems/a97199e0-6bd1-4356-9690-cd4e256aed46
-- title:
--   Countable reciprocal-tail covering of the real line
-- statement:
--   The real line is covered by the nonpositive half-line and the positive reciprocal tails [1/n, infinity) for n positive. This Archimedean covering provides the countable family underlying sigma-finite restrictions of positive-jump Lévy measures.
-- source:
--   Archimedean property of the reals, Real.exists_nat_pos_inv_lt at pinned Mathlib revision.

import Mathlib
open Set

theorem AvramDividend.Classical.gaussian_positive_reciprocal_tail_cover :
    (⋃ n : ℕ, if n = 0 then Iic (0 : ℝ)
      else Ici ((n : ℝ)⁻¹)) = Set.univ := by sorry
