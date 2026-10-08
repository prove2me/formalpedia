-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_fibonacci_search_optimal
-- name    : BellmanDP.Fibonacci.fibonacci_search_optimal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:43:59.818399+00:00
-- url     : https://prove2.me/theorems/611dc598-ecae-4bd2-ae29-7699db735ddd
-- title:
--   Chapter I, Theorem 11 — $\sup L_n = F_n$, the $n$th Fibonacci number
-- statement:
--   Let $F_0 = F_1 = 1$ and $F_n = F_{n-1} + F_{n-2}$ for $n \ge 2$. For $n \ge 0$ let $\mathcal L_n$ be the set of lengths $L > 0$ with the following property: there is a deterministic search procedure, which chooses each evaluation point from the function values observed so far, such that for every function $f$ that is strictly unimodal on $[0, L]$ (strictly increasing up to its maximizer $m$ and strictly decreasing after it) the procedure evaluates $f$ at most $n$ times and announces an interval of length at most $1$ that contains $m$. Then, for every $n$,
--   $$\sup \mathcal L_n = F_n .$$
--
--   This is Kiefer's theorem on the optimality of Fibonacci search, as proved by Bellman: $n$ evaluations reduce an interval of uncertainty for the maximizer by at most the factor $F_n$, and Fibonacci search achieves every factor below it.
--
--   **Formalization Note** Stated as `IsLUB (feasibleLengths n) (bookFib n)` for every `n`, including $n = 0$ (the book calls $F_0$ a convention; in this model the supremum for $n = 0$ is $1$). The supremum is not attained for $n \ge 2$, which is why the book writes $\sup$. In Mathlib's indexing $F_n$ is `Nat.fib (n + 1)`.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, Theorem 11, p. 34

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, *Dynamic Programming*, Ch. I, § 22, Theorem 11, p. 34: `F_n = Sup L_n` is the `n`th
Fibonacci number (`F₀ = F₁ = 1`, `F_n = F_{n−1} + F_{n−2}` for `n ≥ 2`): for every `n`, the least
upper bound of the lengths `L` of intervals `[0, L]` on which `n` adaptively chosen evaluations
always locate the maximum of a strictly unimodal function within a sub-interval of unit length is
`bookFib n`. -/
theorem fibonacci_search_optimal (n : ℕ) :
    IsLUB (feasibleLengths n) (bookFib n : ℝ) := by sorry

end BellmanDP.Fibonacci
