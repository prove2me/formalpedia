-- Prove2me | Theorems.Thm_Brocard_berndt_galway_search
-- name    : Brocard.berndt_galway_search
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:46:06.098982+00:00
-- url     : https://prove2.me/theorems/b3884934-e136-40f6-8129-d1c16b13257a
-- title:
--   Berndt–Galway: no new solutions of $n!+1=m^2$ with $n < 10^9$
-- statement:
--   Let $n$ and $m$ be natural numbers with $n < 10^9$. If
--   $$n! + 1 = m^2,$$
--   then $n = 4$, $n = 5$ or $n = 7$.
--
--   This records the computer search of Berndt and Galway (2000), which found no solutions of Brocard's equation other than the three known ones below $10^9$. It is the goal restricted to $n < 10^9$ (on the $n$-coordinate).
--
--   **Formalization Note** The bound is taken strict ($n < 10^9$), which is the weaker reading of the reported search range.
-- source:
--   B. C. Berndt and W. F. Galway, On the Brocard–Ramanujan Diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), 41–42; Formal Conjectures library (Google DeepMind, Apache-2.0), FormalConjectures/Wikipedia/BrocardProblem.lean (pointing to FormalConjectures/ErdosProblems/398.lean), https://github.com/google-deepmind/formal-conjectures ; https://en.wikipedia.org/wiki/Brocard%27s_problem ; https://www.erdosproblems.com/398

import Mathlib

namespace Brocard

theorem berndt_galway_search (n m : ℕ) (hn : n < 10 ^ 9)
    (h : Nat.factorial n + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by sorry

end Brocard
