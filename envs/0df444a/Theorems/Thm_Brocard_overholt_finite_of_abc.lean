-- Prove2me | Theorems.Thm_Brocard_overholt_finite_of_abc
-- name    : Brocard.overholt_finite_of_abc
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T22:50:56.818504+00:00
-- url     : https://prove2.me/theorems/9ad3bfd6-8c5b-4931-87dd-1b59d8e112e4
-- title:
--   Overholt: the abc conjecture implies $n!+1=m^2$ has finitely many solutions
-- statement:
--   Assume the abc conjecture: for every $\varepsilon > 0$ there is $K_\varepsilon > 0$ such that $c < K_\varepsilon \operatorname{rad}(abc)^{1+\varepsilon}$ for all positive integers $a, b$ with $\gcd(a,b) = 1$ and $c = a + b$, where $\operatorname{rad}(N)$ is the product of the distinct primes dividing $N$. Then the set
--   $$\{(n, m) \in \mathbb{N} \times \mathbb{N} : n! + 1 = m^2\}$$
--   is finite.
--
--   This is Overholt's conditional finiteness theorem for Brocard's equation (1993).
--
--   **Formalization Note** Overholt's argument needs only a weak form of the abc conjecture; the hypothesis here is the standard form (see the definition file `Brocard_Defs`), which implies the weak form. The abc conjecture is a hypothesis of the theorem, not an assumption of the platform.
-- source:
--   M. Overholt, The Diophantine equation n! + 1 = m^2, Bull. London Math. Soc. 25 (1993), 104; Formal Conjectures library (Google DeepMind, Apache-2.0), FormalConjectures/Wikipedia/BrocardProblem.lean (pointing to FormalConjectures/ErdosProblems/398.lean), https://github.com/google-deepmind/formal-conjectures ; https://en.wikipedia.org/wiki/Brocard%27s_problem ; https://www.erdosproblems.com/398

import Mathlib
import Definitions.Def_Brocard_Defs

namespace Brocard

theorem overholt_finite_of_abc (habc : ABCConjecture) :
    {p : ℕ × ℕ | Nat.factorial p.1 + 1 = p.2 ^ 2}.Finite := by sorry

end Brocard
