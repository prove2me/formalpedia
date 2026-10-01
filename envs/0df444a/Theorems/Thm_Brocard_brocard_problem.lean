-- Prove2me | Theorems.Thm_Brocard_brocard_problem
-- name    : Brocard.brocard_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:55:38.582795+00:00
-- url     : https://prove2.me/theorems/155962b9-2f92-4c7b-b9f7-570c3ddbf0d5
-- title:
--   Brocard's problem: $n! + 1 = m^2$ exactly for $(n,m) = (4,5), (5,11), (7,71)$
-- statement:
--   **Brocard's problem.** The pairs $(n, m)$ of natural numbers satisfying
--   $$n! + 1 = m^2$$
--   are exactly $(4, 5)$, $(5, 11)$ and $(7, 71)$. Equivalently: $n! + 1$ is a perfect square if and only if $n \in \{4, 5, 7\}$, and in those cases $n! + 1$ equals $5^2 = 25$, $11^2 = 121$ and $71^2 = 5041$ respectively.
--
--   This is the Brocard–Ramanujan problem (Erdős problem #398), open since 1876. Pairs with $n! + 1 = m^2$ are called Brown numbers.
--
--   **Formalization Note** The statement is an equality of sets of ordered pairs in $\mathbb{N} \times \mathbb{N}$; $m$ ranges over natural numbers, and $0! = 1$.
-- source:
--   Brocard's problem / Brocard–Ramanujan equation; Erdős problem #398. Formal Conjectures library (Google DeepMind, Apache-2.0), FormalConjectures/Wikipedia/BrocardProblem.lean (pointing to FormalConjectures/ErdosProblems/398.lean), https://github.com/google-deepmind/formal-conjectures ; https://en.wikipedia.org/wiki/Brocard%27s_problem ; https://www.erdosproblems.com/398

import Mathlib

namespace Brocard

theorem brocard_problem :
    {p : ℕ × ℕ | Nat.factorial p.1 + 1 = p.2 ^ 2} = {(4, 5), (5, 11), (7, 71)} := by sorry

end Brocard
