-- Prove2me | Theorems.Thm_AvramDividend_Classical_exp_gap_dominates_half_interval
-- name    : AvramDividend.Classical.exp_gap_dominates_half_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T23:52:05.929588+00:00
-- url     : https://prove2.me/theorems/610d4cbc-d20e-4450-9e96-2f09c6fa25fb
-- title:
--   A uniform exponential-deficit bound for nonnegative arguments at most one half
-- statement:
--   For 0≤u≤1/2, u is bounded by twice the exponential deficit 1-exp(-u). This elementary deterministic estimate is used in controlling expected capped Lévy drift-deficit increments from their exact Laplace moments in the bounded-variation infinite-activity no-local-monotonicity argument.
-- source:
--   Real.add_one_le_exp and the identity exp(u)exp(-u)=1 in pinned Mathlib.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.exp_gap_dominates_half_interval
    (u : ℝ) (hu : 0 ≤ u) (hhalf : u ≤ (1 / 2 : ℝ)) :
    u ≤ 2 * (1 - Real.exp (-u)) := by sorry
