-- Prove2me | Theorems.Thm_AppliedComb_GenFun_newton_binomial
-- name    : AppliedComb.GenFun.newton_binomial
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:12:45.669784+00:00
-- url     : https://prove2.me/theorems/f510a99d-9ff6-4c3b-9f0a-43deb2c98186
-- title:
--   Theorem 8.10 — Newton's Binomial Theorem (pinned: real x with |x| < 1)
-- statement:
--   Let $p$ be a real number with $p \ne 0$, and let $\binom{p}{n} = P(p, n)/n!$ be the generalized binomial coefficient of Definition 8.9. Then for every real number $x$ with $|x| < 1$ the series $\sum_{n \ge 0} \binom{p}{n} x^n$ converges, and
--
--   $$(1 + x)^p = \sum_{n=0}^{\infty} \binom{p}{n} x^n .$$
--
--   When $p$ is a positive integer all terms with $n > p$ vanish and this is the ordinary binomial theorem. In the chapter the theorem is used with $p = -1/2$ to find the generating function of the central binomial coefficients (Theorem 8.13).
--
--   **Formalization Note.** This is the *pinned analytic reading* of the book's Theorem 8.10. The book states the identity without a domain for $x$ and without proof (it refers to advanced calculus texts), while its generating functions are otherwise formal power series, for which $(1+x)^p$ with real $p$ has no meaning until it is defined. Here $x$ is real with $|x| < 1$ (the disc of convergence), $(1 + x)^p$ is the real power `Real.rpow` of the positive number $1 + x$, and the equality is `HasSum`, i.e. unconditional convergence of the series to that value (for a real power series inside its disc of convergence this is the same as absolute convergence). The book's hypothesis $p \ne 0$ is kept although the identity also holds at $p = 0$. The platform theorem `FamousTheorems.newton_binomial_series_6b` states the complex-analytic version with Mathlib's `binomialSeries`; this item states it with the book's own coefficients `binomReal`.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 166, Theorem 8.10 (Newton's Binomial Theorem)

import Mathlib
import Definitions.Def_AppliedComb_GenFun_binomReal

namespace AppliedComb.GenFun

/-- Keller–Trotter, Theorem 8.10 (Newton's Binomial Theorem, p. 166), pinned analytic reading:
for every real `p ≠ 0` and every real `x` with `|x| < 1`, the series
`∑_{n ≥ 0} C(p, n) xⁿ` converges to `(1 + x)^p`, with `C(p, n)` the generalized binomial
coefficient of Definition 8.9 and `(1 + x)^p` the real power of the positive number `1 + x`.
The book gives no domain for `x` and no proof; `|x| < 1` is the disc of convergence. -/
theorem newton_binomial (p : ℝ) (hp : p ≠ 0) (x : ℝ) (hx : |x| < 1) :
    HasSum (fun n : ℕ => binomReal p n * x ^ n) ((1 + x) ^ p) := by sorry

end AppliedComb.GenFun
