-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_upper_bound_recursion
-- name    : BellmanDP.Fibonacci.upper_bound_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:43:43.241472+00:00
-- url     : https://prove2.me/theorems/685e6b08-5089-4212-ae36-93ab7917e30e
-- title:
--   Chapter I, Eq. (22.3) — $L_n < F_{n-1} + F_{n-2}$ for every searchable length
-- statement:
--   Let $n \ge 2$ and let $L > 0$ be a length such that some deterministic adaptive procedure, evaluating a strictly unimodal function $f$ on $[0, L]$ at most $n$ times, always announces an interval of length at most $1$ containing the maximizer of $f$. Then
--   $$L < F_{n-1} + F_{n-2},$$
--   where $F_0 = F_1 = 1$, $F_k = F_{k-1} + F_{k-2}$. In particular $\sup \mathcal L_n \le F_{n-1} + F_{n-2}$, which is Bellman's inequality (22.3).
--
--   This is the optimality half of Theorem 11: no search procedure, however adaptive, does better than the Fibonacci recursion allows.
--
--   **Formalization Note** Bellman proves (3) by induction on $n$, assuming Theorem 11 for smaller indices; the statement here is the unconditional conclusion, for every $n \ge 2$. The subtractions $n - 1$, $n - 2$ are on natural numbers and are exact because $n \ge 2$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, Eq. (22.3), pp. 35-36

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, Eq. (22.3), pp. 35–36: `F_n ≤ F_{n−1} + F_{n−2}`, in the form the proof
establishes it ("in all cases `L_n < F_{n−1} + F_{n−2}`"): for `n ≥ 2`, every interval length on
which `n` evaluations always locate the maximum within unit length is strictly less than
`F_{n−1} + F_{n−2}`. -/
theorem upper_bound_recursion (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL : L ∈ feasibleLengths n) :
    L < (bookFib (n - 1) : ℝ) + bookFib (n - 2) := by sorry

end BellmanDP.Fibonacci
