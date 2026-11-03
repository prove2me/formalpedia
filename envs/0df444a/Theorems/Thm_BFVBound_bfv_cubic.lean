-- Prove2me | Theorems.Thm_BFVBound_bfv_cubic
-- name    : BFVBound.bfv_cubic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T14:44:38.908481+00:00
-- url     : https://prove2.me/theorems/608e7fd7-6574-45e5-948b-55b93464de63
-- title:
--   BFV cubic bound: $F(s)\ge 0.8488\,s+0.08488\,s^3$ on $[0,1]$ for the product-state expectation
-- statement:
--   **The BFV cubic bound for the quantum max-cut product rounding.**
--
--   Let $F$ be the product-state expectation of the BFV/GP rounding of a quantum max-cut relaxation,
--   $$F(s)=c\,s\,G(s^2),\qquad c=\frac{8}{3\pi},\qquad G={}_2F_1\!\left(\tfrac12,\tfrac12;2;\,\cdot\,\right),$$
--   where $s=\tfrac13\operatorname{Tr}[(X_iX_j+Y_iY_j+Z_iZ_j)\rho]\in[-1,\tfrac13]$ is the *Pauli correlation* of an
--   edge and $F(s)=\mathbb{E}[t_{ij}]$ is the expected correlation produced by product rounding
--   (Brandão–Fernandes–Vallentin; Goemans–Williamson; ALMPS25 Eq. (17), PT22 Eq. (3)).
--
--   **Theorem.** For every $s\in[0,1]$,
--   $$F(s)\;\ge\;0.8488\,s+0.08488\,s^{3}.$$
--
--   **Why it matters.** $0.8488=8/(3\pi)$ is the BFV rank-three constant, i.e. the value of $F'(0)$; the cubic term
--   is the next Taylor coefficient. This per-edge inequality is exactly the product side of the two-parameter
--   mixing bound that the platform's quantum max-cut campaign consumes in its proved scalar
--   `CubicMatching.lp24_strict_scalar`: combined with the matching side, it yields the $0.595$ / $0.614$
--   approximation ratios via $F(s)\ge\gamma_1 s+\gamma_3 s^3$.
--
--   **Proof sketch.** The hypergeometric coefficients $a_n=\big((\tfrac12)_n\big)^2/\big((2)_n\,n!\big)$ satisfy
--   $a_{n+1}/a_n=(n+\tfrac12)^2/\big((n+1)(n+2)\big)\le 1$, so $a_0=1$, $a_1=\tfrac18$, all $a_n\ge0$ and
--   $a_n\le 2/\big((n+1)(n+2)\big)$ (summable, telescoping to $2$). Hence $G(x)\ge 1+x/8$ for $0\le x\le 1$
--   (first two terms plus nonnegativity), and $\pi\ge 3.14159$ gives $8/(3\pi)\ge 0.8488$; multiplying
--   $0.8488\,s+0.08488\,s^3\le(8/(3\pi))\,s\,(1+s^2/8)$ by $s\ge0$ finishes.
--
--   *Formalization note.* The statement is a theorem about the published definition
--   `QuantumMaxCutBFVProductRounding`; the series is not assumed to be the classical ${}_2F_1$ but *defined* as the
--   power series $\sum_n a_n x^n$ with those coefficients (so no special-function library is needed).
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 (ESA 2025), Section 4.2 Eq. (17); Parekh-Thompson arXiv:2110.07781 Eq. (3); Brandao-Fernandes-Vallentin arXiv:0910.5765 (rank-three constant 8/(3\pi)); the cubic itself is the polynomial of LP24 (arXiv:2401.03616) Eq. (8) as published on this platform in CubicMatching.lp24_strict_scalar.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace BFVBound

theorem bfv_cubic (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    (0.8488 : ℝ) * s + 0.08488 * s ^ 3 ≤ F s := by sorry

end BFVBound
