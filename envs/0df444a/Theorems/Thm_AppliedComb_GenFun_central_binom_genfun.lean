-- Prove2me | Theorems.Thm_AppliedComb_GenFun_central_binom_genfun
-- name    : AppliedComb.GenFun.central_binom_genfun
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:13:00.846987+00:00
-- url     : https://prove2.me/theorems/6e0a59cb-9809-4402-9a6b-088ae97a4592
-- title:
--   Theorem 8.13 — (1 − 4x)^{−1/2} generates the central binomial coefficients
-- statement:
--   The function $f(x) = (1 - 4x)^{-1/2}$ is the generating function of the sequence $\{\binom{2n}{n} : n \ge 0\}$ of central binomial coefficients: for every real number $x$ with $|x| < 1/4$ the series $\sum_{n\ge 0}\binom{2n}{n}x^n$ converges, and
--
--   $$(1 - 4x)^{-1/2} = \sum_{n=0}^{\infty} \binom{2n}{n} x^n .$$
--
--   Squaring this function gives $1/(1-4x)$, which is how the chapter derives the central binomial convolution (Corollary 8.14); the same generating function returns in Section 9.7 of the book.
--
--   **Formalization Note.** This is the *pinned analytic reading*, the same as for Theorem 8.10: "generating function" is read as convergence of the power series to $f(x)$ on the disc $|x| < 1/4$, where $1 - 4x > 0$ and $(1-4x)^{-1/2}$ is `Real.rpow`. It is not the purely formal statement $A(X)^2(1 - 4X) = 1$ in $\mathbb{Q}[[X]]$ for $A = \sum \binom{2n}{n} X^n$, which is a different (and weaker-looking) claim.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 167, Theorem 8.13

import Mathlib

namespace AppliedComb.GenFun

/-- Keller–Trotter, Theorem 8.13 (p. 167), pinned analytic reading: the function
`f(x) = (1 - 4x)^(-1/2)` is the generating function of the sequence `{C(2n, n) : n ≥ 0}`,
that is, for every real `x` with `|x| < 1/4` the series `∑_{n ≥ 0} C(2n, n) xⁿ` converges to
`(1 - 4x)^(-1/2)` (a real power of the positive number `1 - 4x`). -/
theorem central_binom_genfun (x : ℝ) (hx : |x| < 1 / 4) :
    HasSum (fun n : ℕ => ((Nat.choose (2 * n) n : ℕ) : ℝ) * x ^ n)
      ((1 - 4 * x) ^ (-(1 / 2 : ℝ))) := by sorry

end AppliedComb.GenFun
