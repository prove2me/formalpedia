-- Prove2me | Theorems.Thm_ChebyshevFunctions_sum_log_eq_sum_vonMangoldt_mul_div
-- name    : ChebyshevFunctions.sum_log_eq_sum_vonMangoldt_mul_div
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:52.465747+00:00
-- url     : https://prove2.me/theorems/c2c3cda1-02d9-44e4-98d0-97df73491079
-- title:
--   $\log(N!)$ as a von Mangoldt sum
-- statement:
--   **Legendre's factorial identity.**
--
--   For every $N$,
--
--   $$\log(N!) \;=\; \sum_{n \le N} \log n \;=\; \sum_{d \le N} \Lambda(d)\left\lfloor \frac{N}{d}\right\rfloor ,$$
--
--   where $\Lambda$ is the von Mangoldt function.
--
--   The identity comes from $\log n = \sum_{d \mid n}\Lambda(d)$ — itself the statement that
--   $\Lambda \star 1 = \log$ — summed over $n \le N$ and with the order of summation exchanged: each
--   $d$ contributes $\Lambda(d)$ once for every multiple of $d$ up to $N$, and there are exactly
--   $\lfloor N/d \rfloor$ of those.
--
--   This is the starting point of Chebyshev's elementary theory of the distribution of primes.
--   Combining it with Stirling's estimate $\log(N!) = N\log N - N + O(\log N)$ and removing the
--   floor functions yields $\sum_{d \le N}\Lambda(d)/d = \log N + O(1)$, hence Mertens' theorems and
--   the bounds $\theta(N) \asymp N$ — all without any complex analysis.
--
--   **Formalization note.** The sums run over `Finset.Ioc 0 N`, i.e. $1 \le n \le N$, avoiding
--   $\log 0$; `N / d` is natural division, so the cast to $\mathbb{R}$ is the floor
--   $\lfloor N/d\rfloor$.
-- source:
--   Classical; Legendre's identity, see Apostol, *Introduction to Analytic Number Theory*, §4.2, and Montgomery & Vaughan, §2.1. Lean proof extracted from `Salt/Maynard/Mertens.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace ChebyshevFunctions

open ArithmeticFunction in
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n
      = ∑ d ∈ Finset.Ioc 0 N, vonMangoldt d * ((N / d : ℕ) : ℝ) := by sorry

end ChebyshevFunctions
