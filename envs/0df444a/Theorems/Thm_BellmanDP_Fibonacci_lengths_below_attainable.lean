-- Prove2me | Theorems.Thm_BellmanDP_Fibonacci_lengths_below_attainable
-- name    : BellmanDP.Fibonacci.lengths_below_attainable
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-02T14:43:49.634984+00:00
-- url     : https://prove2.me/theorems/0d6e30e1-d57d-40a7-8c9d-096917f4ebb4
-- title:
--   Chapter I, § 22 — every length below $F_{n-1} + F_{n-2}$ is searchable with $n$ evaluations
-- statement:
--   Let $n \ge 2$ and $0 < L < F_{n-1} + F_{n-2}$. Then there is a deterministic adaptive procedure that, for every function $f$ strictly unimodal on $[0, L]$, evaluates $f$ at most $n$ times and announces an interval of length at most $1$ containing the maximizer of $f$; that is,
--   $$L \in \mathcal L_n .$$
--
--   Together with (22.3) this gives $\sup \mathcal L_n = F_{n-1} + F_{n-2}$: the Fibonacci search, which places the first two points close to $F_{n-2}$ and $F_{n-1}$ and reuses the surviving point at every later step, achieves the bound.
--
--   **Formalization Note** The natural-number subtractions $n - 1$, $n - 2$ are exact because $n \ge 2$.
-- source:
--   Bellman, Dynamic Programming, Princeton University Press (1957; Princeton Landmarks ed. 2010), DOI 10.2307/j.ctv1nxcw0f, Chapter I, § 22, proof of Theorem 11, p. 36

import Mathlib
import Definitions.Def_BellmanDP_Fibonacci_SearchModel

namespace BellmanDP.Fibonacci

/-- Bellman, Ch. I, § 22, proof of Theorem 11, p. 36: choosing `L_n`, `x₁`, `x₂` arbitrarily close
to their upper bounds gives `F_n = F_{n−1} + F_{n−2}`: for `n ≥ 2`, every length
`0 < L < F_{n−1} + F_{n−2}` admits a procedure that always locates the maximum within unit length
using at most `n` evaluations. -/
theorem lengths_below_attainable (n : ℕ) (hn : 2 ≤ n) (L : ℝ) (hL0 : 0 < L)
    (hL : L < (bookFib (n - 1) : ℝ) + bookFib (n - 2)) :
    L ∈ feasibleLengths n := by sorry

end BellmanDP.Fibonacci
