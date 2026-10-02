-- Prove2me | Theorems.Thm_AppliedComb_GenFun_genfun_mul
-- name    : AppliedComb.GenFun.genfun_mul
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T01:13:22.708595+00:00
-- url     : https://prove2.me/theorems/06a6e3df-75b7-4f35-b095-0cfbeb2e57af
-- title:
--   Proposition 8.3 — coefficients of a product of generating functions
-- statement:
--   Let $a = (a_n)_{n\ge0}$ and $b = (b_n)_{n\ge0}$ be sequences of real numbers with generating functions $A(x) = \sum_{n=0}^{\infty} a_n x^n$ and $B(x) = \sum_{n=0}^{\infty} b_n x^n$, regarded as formal power series. Then $A(x)B(x)$ is the generating function of the sequence whose $n$-th term is
--
--   $$a_0 b_n + a_1 b_{n-1} + a_2 b_{n-2} + \cdots + a_n b_0 = \sum_{k=0}^{n} a_k b_{n-k}.$$
--
--   This is the rule by which products of generating functions encode convolutions; Corollary 8.14 is obtained from it by squaring the generating function of Theorem 8.13.
--
--   **Formalization Note.** Generating functions are Mathlib formal power series `PowerSeries ℝ`, with $A$ = `PowerSeries.mk a` (the book, p. 157, treats them as formal power series over the reals). The sum is over `Finset.range (n + 1)`, i.e. $k = 0, \dots, n$, so the natural-number subtraction $n - k$ is exact.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 159, Proposition 8.3

import Mathlib

namespace AppliedComb.GenFun

/-- Keller–Trotter, Proposition 8.3 (p. 159): if `A(x) = ∑ aₙ xⁿ` and `B(x) = ∑ bₙ xⁿ` are the
generating functions (formal power series) of real sequences `a` and `b`, then `A(x)B(x)` is
the generating function of the sequence whose `n`-th term is
`a₀bₙ + a₁bₙ₋₁ + ⋯ + aₙb₀ = ∑_{k=0}^{n} a_k b_{n-k}`. -/
theorem genfun_mul (a b : ℕ → ℝ) :
    PowerSeries.mk a * PowerSeries.mk b =
      PowerSeries.mk (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), a k * b (n - k)) := by sorry

end AppliedComb.GenFun
