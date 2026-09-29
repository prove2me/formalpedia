-- Prove2me | Theorems.Thm_DivisorSums_sum_card_divisors_le
-- name    : DivisorSums.sum_card_divisors_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:06:53.346165+00:00
-- url     : https://prove2.me/theorems/0c8ef581-3132-4a6f-ae7d-c7379f1be6bb
-- title:
--   The Dirichlet divisor sum is at most $x(1+\log x)$
-- statement:
--   **An explicit bound for the summatory divisor function.**
--
--   For every $x \ge 1$,
--
--   $$\sum_{n \le x} d(n) \;\le\; x\bigl(1 + \log x\bigr).$$
--
--   The classical Dirichlet asymptotic is
--   $\sum_{n\le x} d(n) = x\log x + (2\gamma-1)x + O(\sqrt x)$, so the bound above has the correct
--   main term $x\log x$ and is **explicit**, valid for all $x \ge 1$ with no implied constant.
--
--   The proof is the hyperbola-free counting argument: interchanging summation,
--
--   $$\sum_{n \le x} d(n) = \sum_{n\le x}\sum_{d \mid n} 1 = \sum_{d \le x}\left\lfloor\frac{x}{d}\right\rfloor
--   \;\le\; x\sum_{d\le x}\frac1d \;\le\; x\,(1 + \log x),$$
--
--   the last step by comparing the harmonic sum with $\int_1^x dt/t$.
--
--   On average, then, an integer up to $x$ has about $\log x$ divisors — in sharp contrast with the
--   maximal order of $d(n)$, which is $n^{o(1)}$ but far larger than $\log n$ infinitely often.
--   Explicit bounds of this shape are what let a divisor factor be absorbed in a sum without
--   invoking an asymptotic.
--
--   **Formalization note.** `n.divisors.card` is $d(n)$; the sum runs over $1 \le n \le x$.
-- source:
--   Classical; Dirichlet's divisor problem, see Apostol, *Introduction to Analytic Number Theory*, §3.3. Lean proof extracted from `Salt/BV/` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DivisorSums

theorem sum_card_divisors_le (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ≤ x * (1 + Real.log x) := by sorry

end DivisorSums
