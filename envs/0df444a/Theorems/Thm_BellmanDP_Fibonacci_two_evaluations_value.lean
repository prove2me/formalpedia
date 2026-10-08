-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_two_evaluations_value
-- name    : BellmanDP.Fibonacci.two_evaluations_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:43:35.528914+00:00
-- url     : https://prove2.me/theorems/c9348bc8-d29f-4fe4-bec6-d7879afc1498
-- title:
--   Chapter I, § 22 — with two evaluations, $\sup L_2 = F_2 = 2$
-- statement:
--   Let $\mathcal L_2$ be the set of lengths $L > 0$ such that some deterministic adaptive procedure, evaluating a strictly unimodal function $f$ on $[0, L]$ at most twice, always announces an interval of length at most $1$ containing the maximizer of $f$. Then
--   $$\sup \mathcal L_2 = 2 = F_1 + F_0 .$$
--
--   Every length $2 - \varepsilon$ is searchable (evaluate at $1 - \varepsilon$ and $1$ and compare), while the supremum itself is not attained. This is the first case in which comparing two values gains information.
--
--   **Formalization Note** Stated as `IsLUB (feasibleLengths 2) 2`; the statement does not assert that $2 \notin \mathcal L_2$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, proof of Theorem 11, p. 35

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, proof of Theorem 11, p. 35: for `n = 2`, `L₂ = 2 − ε` is attainable
(`x₁ = 1 − ε`, `x₂ = 1`) for arbitrarily small `ε > 0`, and `F₂ = 2 = F₁ + F₀`. -/
theorem two_evaluations_value :
    IsLUB (feasibleLengths 2) (2 : ℝ) := by sorry

end BellmanDP.Fibonacci
