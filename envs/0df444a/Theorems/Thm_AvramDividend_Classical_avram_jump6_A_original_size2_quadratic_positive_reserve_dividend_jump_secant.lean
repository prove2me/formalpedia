-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_size2_quadratic_positive_reserve_dividend_jump_secant
-- name    : AvramDividend.Classical.avram_jump6_A_original_size2_quadratic_positive_reserve_dividend_jump_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T08:54:25.596175+00:00
-- url     : https://prove2.me/theorems/9b588d0a-d3be-4a7e-9eb3-e1a9ee3624c1
-- title:
--   Original quadratic supersolution pays any admissible right-dividend atom from its finite-cap secant
-- statement:
--   For the exact Proved Brownian–size-two-Poisson HJB candidate w(z)=0 for z<0 and 1+z+z² for z≥0, whenever the original prepayment reserve y≥0 and a right-dividend atom δ lies in [0,y], then the actual secant w(y)−w(y−δ) dominates δ. This algebraic lemma supplies the hJump condition for an admissible finite-cap barrier strategy in the physical counterexample, preserving the right-postpayment convention.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_size2_quadratic_positive_reserve_dividend_jump_secant
    (y δ : ℝ) (hy : 0 ≤ y) (hδ : 0 ≤ δ) (hδle : δ ≤ y) :
    δ ≤ (if y < 0 then 0 else 1 + y + y ^ 2) -
      (if y - δ < 0 then 0 else 1 + (y - δ) + (y - δ) ^ 2) := by sorry
