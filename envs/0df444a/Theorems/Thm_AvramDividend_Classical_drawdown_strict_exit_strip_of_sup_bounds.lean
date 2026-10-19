-- Prove2me | Theorems.Thm_AvramDividend_Classical_drawdown_strict_exit_strip_of_sup_bounds
-- name    : AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T05:42:05.41666+00:00
-- url     : https://prove2.me/theorems/45e397da-f6fa-4eb0-a294-6c3ab2c5f2c5
-- title:
--   Strict drawdown versus ordinary exit bounds before the next record height
-- statement:
--   Suppose S is a running-supremum value before the process first reaches its next record height h, so 0≤S≤h. For its present value X and positive drawdown barrier a, falling below −a necessarily breaches the strict reflected drawdown barrier S−X>a; conversely breaching that reflected barrier forces X<h−a. The two corresponding survival implications also hold. These four elementary inequalities are the pointwise foundation for the inclusions of killed-upcrossing events needed in the two-sided scale-exit renewal proof of the reflected-supremum discounted dividend value. This statement does not assert a stopping-time law, two-sided scale exit formula, or the final valuation identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1 and the killed-reflected-supremum argument; elementary sandwich S−a∈[−a,h−a] when S∈[0,h].

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem AvramDividend.Classical.drawdown_strict_exit_strip_of_sup_bounds
    (a h S X : ℝ) (hS0 : 0 ≤ S) (hSh : S ≤ h) :
    (X < -a → a < S - X) ∧
    (a < S - X → X < h - a) ∧
    (h - a ≤ X → S - X ≤ a) ∧
    (S - X ≤ a → -a ≤ X) := by sorry
