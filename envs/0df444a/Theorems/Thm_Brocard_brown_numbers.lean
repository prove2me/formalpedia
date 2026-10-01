-- Prove2me | Theorems.Thm_Brocard_brown_numbers
-- name    : Brocard.brown_numbers
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T22:41:12.258813+00:00
-- url     : https://prove2.me/theorems/26474f3f-a006-4a3f-944a-165523e22298
-- title:
--   The known solutions: $4!+1 = 5^2$, $5!+1 = 11^2$, $7!+1 = 71^2$
-- statement:
--   The three known solutions of Brocard's equation $n! + 1 = m^2$:
--   $$4! + 1 = 5^2, \qquad 5! + 1 = 11^2, \qquad 7! + 1 = 71^2,$$
--   that is, $25 = 25$, $121 = 121$ and $5041 = 5041$.
--
--   These are the pairs $(n, m) = (4, 5), (5, 11), (7, 71)$ (Brown numbers). This milestone is the inclusion of the three known pairs in the solution set, one of the two directions of the mission's goal.
-- source:
--   Brocard, Nouv. Corresp. Math. 2 (1876), 287; Formal Conjectures library (Google DeepMind, Apache-2.0), FormalConjectures/Wikipedia/BrocardProblem.lean (pointing to FormalConjectures/ErdosProblems/398.lean), https://github.com/google-deepmind/formal-conjectures ; https://en.wikipedia.org/wiki/Brocard%27s_problem ; https://www.erdosproblems.com/398

import Mathlib

namespace Brocard

theorem brown_numbers :
    Nat.factorial 4 + 1 = 5 ^ 2 ∧ Nat.factorial 5 + 1 = 11 ^ 2 ∧
      Nat.factorial 7 + 1 = 71 ^ 2 := by sorry

end Brocard
