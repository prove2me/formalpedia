-- Prove2me | Theorems.Thm_FCP_Order_one_third_two_thirds_conjecture
-- name    : FCP.Order.one_third_two_thirds_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:56:08.08616+00:00
-- url     : https://prove2.me/theorems/52aca793-5aeb-48cf-8a58-9226614f4509
-- title:
--   The $1/3$--$2/3$ conjecture
-- statement:
--   **The $1/3$--$2/3$ conjecture (Kislitsyn; Fredman; Linial).** In every finite partially ordered set that is not totally ordered there are two elements $x, y$ such that the proportion of linear extensions in which $x$ precedes $y$ lies in $[1/3, 2/3]$. Equivalently, sorting a finite poset by comparisons always admits a nearly balanced query. The best unconditional bound replaces $1/3$ by $(5-\sqrt5)/10 \approx 0.276$ (Brightwell--Felsner--Trotter); the conjecture is known for width-two posets, for semiorders and for several other classes.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/conjecture_1_3_to_2_3.lean); https://en.wikipedia.org/wiki/1/3%E2%80%932/3_conjecture

import Mathlib
import Definitions.Def_FCP_LinearExtensions

namespace FCP.Order

theorem one_third_two_thirds_conjecture (P : Type) [Fintype P] [PartialOrder P]
    (h_not_total : ¬ ∀ x y : P, x ≤ y ∨ y ≤ x) :
    ∃ x y : P, (({e ∈ LinearExtensions P | e x < e y}.ncard : ℚ) /
      (LinearExtensions P).ncard) ∈ Set.Icc (1 / 3 : ℚ) (2 / 3) := by sorry

end FCP.Order
