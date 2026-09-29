-- Prove2me | Theorems.Thm_DirichletLFunctions_LSeriesSummable_toArithmeticFunction
-- name    : DirichletLFunctions.LSeriesSummable_toArithmeticFunction
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:02:30.441342+00:00
-- url     : https://prove2.me/theorems/29f41301-6094-451d-a99e-45d4dfb86b38
-- title:
--   A character's $L$-series converges absolutely for $\Re s>1$
-- statement:
--   **The Dirichlet series of a character converges absolutely on $\Re s > 1$.**
--
--   For any Dirichlet character $\chi$ modulo $N$ and any $s$ with $\Re s > 1$, the series
--
--   $$\sum_{n \ge 1} \frac{\chi(n)}{n^{s}}$$
--
--   is absolutely summable.
--
--   Characters are bounded: $|\chi(n)| \le 1$ for every $n$, with value $0$ off the units. Hence
--   $|\chi(n)n^{-s}| \le n^{-\Re s}$, and $\sum_n n^{-\sigma}$ converges exactly when $\sigma > 1$.
--   So the abscissa of absolute convergence is at most $1$, uniformly over all characters and all
--   moduli.
--
--   Summability is the hypothesis every series manipulation requires — rearrangement, Euler
--   product expansion, term-by-term differentiation, and the convolution identity
--   $\mathrm{LSeries}(f \star g) = \mathrm{LSeries}(f)\,\mathrm{LSeries}(g)$ all need it. Recording
--   it once for characters saves rediscovering the bound at each use.
--
--   **Formalization note.** `LSeriesSummable f s` is Mathlib's absolute summability of the terms
--   $f(n)n^{-s}$; `toArithmeticFunction` coerces $\chi$ into `ArithmeticFunction ℂ`.
-- source:
--   Classical; see Apostol, *Introduction to Analytic Number Theory*, §11.1. Lean proof extracted from `Salt/SW/FourFold.lean` of the Salt project, https://github.com/jyh/salt (Apache-2.0, Jason Hickey).

import Mathlib

namespace DirichletLFunctions

open ArithmeticFunction in
theorem LSeriesSummable_toArithmeticFunction {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (toArithmeticFunction (χ ·)) s := by sorry

end DirichletLFunctions
