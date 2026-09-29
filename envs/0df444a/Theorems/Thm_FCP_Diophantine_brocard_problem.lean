-- Prove2me | Theorems.Thm_FCP_Diophantine_brocard_problem
-- name    : FCP.Diophantine.brocard_problem
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:23:06.923525+00:00
-- url     : https://prove2.me/theorems/7f39ede6-58f7-41a5-a455-65a5448d9fe7
-- title:
--   Brocard's problem: $n! + 1 = m^2$ only for $n = 4, 5, 7$
-- statement:
--   **Brocard's problem.** The only natural numbers $n$ for which $n! + 1$ is a perfect square are $n = 4$, $n = 5$ and $n = 7$ (giving $25 = 5^2$, $121 = 11^2$ and $5041 = 71^2$). Pairs $(n, m)$ with $n! + 1 = m^2$ are called Brown numbers; Erdős conjectured that only these three exist, and searches have found no others up to $10^{9}$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/BrocardProblem.lean, FormalConjectures/ErdosProblems/398.lean); https://en.wikipedia.org/wiki/Brocard%27s_problem

import Mathlib

open Nat

namespace FCP.Diophantine

theorem brocard_problem (n m : ℕ) (h : n ! + 1 = m ^ 2) : n = 4 ∨ n = 5 ∨ n = 7 := by sorry

end FCP.Diophantine
