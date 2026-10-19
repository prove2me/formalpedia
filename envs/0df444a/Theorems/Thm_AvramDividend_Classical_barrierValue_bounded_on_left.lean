-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_bounded_on_left
-- name    : AvramDividend.Classical.barrierValue_bounded_on_left
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T06:01:11.300552+00:00
-- url     : https://prove2.me/theorems/4c051a4e-7444-4318-a49b-a947f304f153
-- title:
--   The barrier value function is bounded on each left half-line under scale monotonicity
-- statement:
--   For W nonnegative and nondecreasing on [0,infinity), a nonnegative finite barrier a and x>a, the piecewise barrierValue W a is uniformly bounded in absolute value for all z<=x. The result includes negative reserves, the nonlinear W branch, and the affine tail, and accommodates extended-real scale derivatives and totalised real division.

import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Set
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierValue_bounded_on_left
    (W : ℝ → ℝ) (a x : ℝ) (ha : 0 ≤ a) (hx : a < x)
    (hn : ∀ z, 0 ≤ z → 0 ≤ W z)
    (hm : MonotoneOn W (Ici 0)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℝ, z ≤ x → |barrierValue W a z| ≤ M := by sorry
