-- Prove2me | Theorems.Thm_AppliedComb_Ramsey_erdos_lower_bound
-- name    : AppliedComb.Ramsey.erdos_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T01:31:55.930658+00:00
-- url     : https://prove2.me/theorems/a0cd840b-43ba-4aa1-aa3a-6e169777c1c8
-- title:
--   Theorem 11.4 (Erdős) — R(n, n) ≥ n/(e√2) · 2^{n/2}
-- statement:
--   Let $R(n, n)$ be the diagonal Ramsey number: the least positive integer $N$ such that every finite simple graph with at least $N$ vertices contains a complete subgraph on $n$ vertices or an independent set of size $n$ (Theorem 11.2). Then for every positive integer $n$,
--   $$R(n, n) \;\ge\; \frac{n}{e\sqrt{2}}\, 2^{\frac{1}{2} n}.$$
--
--   Equivalently, for every integer $N$ with $1 \le N < \frac{n}{e\sqrt2}2^{n/2}$ there is a simple graph on $N$ vertices with no complete subgraph on $n$ vertices and no independent set of size $n$. Together with the upper bound $R(n, n) \le \binom{2n-2}{n-1}$ from the proof of Theorem 11.2, it pins $R(n,n)^{1/n}$ between $\sqrt 2$ and $4$ asymptotically. The result, due to Erdős (1947), is the classical first application of the probabilistic method.
--
--   **Formalization Note.** The bound is stated for every $n \ge 1$, with no asymptotic slack: the book's proof uses Stirling's approximation for $n!$, and an explicit lower bound $n! \ge \sqrt{2\pi n}\,(n/e)^n$ suffices for every $n$. The comparison is in $\mathbb R$, with $2^{n/2}$ a real power; $R(n,n)$ is `ramseyNumber n n` from the definition `AppliedComb.Ramsey.ramseyNumber`. Because the right-hand side is positive, the statement cannot hold through the junk value `sInf ∅ = 0`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 232, Theorem 11.4

import Mathlib
import Definitions.Def_AppliedComb_Ramsey_ramseyNumber

namespace AppliedComb.Ramsey

/-- Theorem 11.4 (Erdős), Keller & Trotter p. 232: for every positive integer `n`,
`R(n, n) ≥ n / (e √2) · 2^{n/2}`, where `R(n, n) = ramseyNumber n n` is the least positive
integer such that every graph with at least that many vertices has an `n`-clique or an
independent set of size `n` (Theorem 11.2). -/
theorem erdos_lower_bound (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / (Real.exp 1 * Real.sqrt 2) * (2 : ℝ) ^ ((n : ℝ) / 2) ≤
      (ramseyNumber n n : ℝ) := by sorry

end AppliedComb.Ramsey
