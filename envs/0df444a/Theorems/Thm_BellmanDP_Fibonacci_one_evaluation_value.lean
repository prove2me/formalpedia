-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_one_evaluation_value
-- name    : BellmanDP.Fibonacci.one_evaluation_value
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:43:14.006402+00:00
-- url     : https://prove2.me/theorems/8505713d-9ba4-4fdc-92c2-576b4460689c
-- title:
--   Chapter I, § 22 — with one evaluation, $\sup L_1 = F_1 = 1$
-- statement:
--   Let $\mathcal L_1$ be the set of lengths $L > 0$ such that some deterministic adaptive procedure, evaluating a strictly unimodal function $f$ on $[0, L]$ at most once, always announces an interval of length at most $1$ containing the maximizer of $f$. Then
--   $$\sup \mathcal L_1 = 1 = F_1 .$$
--
--   A single value of $f$ carries no information about where the maximum lies, so one evaluation is no better than none; this is the base case that fixes the value $F_1$ of Bellman's sequence.
--
--   **Formalization Note** Stated as `IsLUB (feasibleLengths 1) 1`.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, proof of Theorem 11, p. 34

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, proof of Theorem 11, p. 34: "the value of `F₁` is determined by the
process": with one evaluation, `Sup L₁ = 1 = F₁`. -/
theorem one_evaluation_value :
    IsLUB (feasibleLengths 1) (1 : ℝ) := by sorry

end BellmanDP.Fibonacci
