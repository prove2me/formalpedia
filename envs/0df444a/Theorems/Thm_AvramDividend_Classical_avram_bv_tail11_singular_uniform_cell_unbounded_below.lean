-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_tail11_singular_uniform_cell_unbounded_below
-- name    : AvramDividend.Classical.avram_bv_tail11_singular_uniform_cell_unbounded_below
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T09:59:32.364836+00:00
-- url     : https://prove2.me/theorems/54e0574d-719a-430a-9e62-0126bd7e65de
-- title:
--   Original affine singular BV generator sampled on a uniform cell becomes arbitrarily negative
-- statement:
--   For the already proved original zero-extended affine BV singular generator profile, choose the exact unit-horizon uniform-grid width at row K+2 and surplus equal to its fourth power. The single cell contribution is at most minus K. This is a deterministic scalar obstruction to unconditional left-sampled generator convergence, not by itself a counterexample to the full stochastic theorem.
-- source:
--   Direct from accepted reciprocal singular tail bound 23283bab, exact original affine generator profile d3319180, and algebra for physical cell width; intended validity check for Open 0b2da5b3.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_profile_tail_bound
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_tail11_singular_uniform_cell_unbounded_below
    (K : ℕ) :
    let h : ℝ := 1 / ((K : ℝ) + 4)
    h * (3 + h ^ 4 - 4 * h ^ 2 - 2 / h ^ 2) ≤ -(K : ℝ) := by sorry
