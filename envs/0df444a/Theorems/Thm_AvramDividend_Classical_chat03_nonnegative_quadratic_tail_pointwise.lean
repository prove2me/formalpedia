-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_nonnegative_quadratic_tail_pointwise
-- name    : AvramDividend.Classical.chat03_nonnegative_quadratic_tail_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T09:23:59.098232+00:00
-- url     : https://prove2.me/theorems/915d7883-a8b6-4a72-949f-e3ed2e386986
-- title:
--   Nonnegative high-value tail dominated by quadratic moment over threshold
-- statement:
--   For a nonnegative value y and positive threshold R, the upper tail y times its high-value indicator is bounded above by its squared value divided by R. This exact pointwise bound is the elementary step connecting uniform second-moment bounds to uniformly small tails in the open stopped-scale expectation convergence obligation.
-- source:
--   Algebraic inequality using 0≤y(R−y) when y≥R.

import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real

theorem AvramDividend.Classical.chat03_nonnegative_quadratic_tail_pointwise
    (R y : ℝ) (hR : 0 < R) (hy : 0 ≤ y) :
    (if R ≤ y then y else 0) ≤ y ^ 2 / R := by sorry
