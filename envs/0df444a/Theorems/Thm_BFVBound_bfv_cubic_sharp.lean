-- Prove2me | Theorems.Thm_BFVBound_bfv_cubic_sharp
-- name    : BFVBound.bfv_cubic_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T15:02:53.206559+00:00
-- url     : https://prove2.me/theorems/1f10dc65-50eb-4481-b3f9-cf4ad2db0552
-- title:
--   Sharp two-term BFV bound: $F(s)\ge\frac{8}{3\pi}s+\frac{1}{3\pi}s^3$ on $[0,1]$
-- statement:
--   **The sharp two-term BFV product bound.**
--
--   The BFV/GP product rounding of a quantum max-cut relaxation has per-edge expected correlation
--   $$F(s)=\frac{8}{3\pi}\,s\,G(s^{2}),\qquad G={}_2F_1\!\left(\tfrac12,\tfrac12;2;\,\cdot\,\right),$$
--   where $s=\tfrac13\operatorname{Tr}[(X_iX_j+Y_iY_j+Z_iZ_j)\rho]$ is the Pauli correlation of the edge.
--
--   **Theorem.** For every $s\in[0,1]$,
--   $$F(s)\;\ge\;\frac{8}{3\pi}\,s+\frac{1}{3\pi}\,s^{3}.$$
--
--   Because $G(x)=1+\tfrac{x}{8}+\tfrac{3x^2}{64}+\cdots$, the coefficient $\tfrac{1}{3\pi}=\tfrac{8}{3\pi}\cdot\tfrac18$
--   is exactly the third Taylor coefficient of $F$: this is the *sharp* form of the product-side bound, and it implies
--   the decimal form $F(s)\ge 0.8488\,s+0.08488\,s^{3}$ used by the LP24 mixing scalar
--   (`CubicMatching.lp24_strict_scalar`), whose $0.08488$ is a deliberate underestimate of $\tfrac1{3\pi}=0.10610\ldots$.
--
--   **Why it matters.** This is the product side of every quantum max-cut ratio analysis from $0.5$ upward: the
--   per-edge comparison of a rounding algorithm's energy against the level-2 SDP bound $\tfrac12(1-3s)$ needs a lower
--   bound on $F$ on the positive range of $s$, and the second-order truncation is what the existing proved scalars
--   consume.
--
--   **Proof.** The hypergeometric coefficients $a_n=\big((\tfrac12)_n\big)^2/((2)_n n!)$ are nonnegative with
--   $a_0=1$, $a_1=\tfrac18$ and $a_{n+1}/a_n=(n+\tfrac12)^2/((n+1)(n+2))\le1$; dropping all terms of $G$ past the
--   linear one gives $G(x)\ge1+x/8$ for $x\in[0,1]$. Multiplying by $\tfrac{8}{3\pi}s\ge0$ gives
--   $F(s)\ge\tfrac{8}{3\pi}s\bigl(1+\tfrac{s^2}{8}\bigr)=\tfrac{8}{3\pi}s+\tfrac{1}{3\pi}s^3$.
--
--   *Formalization note.* The statement concerns the published definition `QuantumMaxCutBFVProductRounding`; the
--   series is defined as a power series, so no special-function library is involved.
-- source:
--   Anshu, Lee, Mousavi, Parekh, Soleimanifar, arXiv:2504.15276 Section 4.2 Eq. (17); Parekh-Thompson arXiv:2110.07781 Eq. (3); Brandao-Fernandes-Vallentin arXiv:0910.5765 (rank-three constant 8/(3\pi)); the series is 2F1(1/2,1/2;2;x) = sum_n ((1/2)_n)^2/((2)_n n!) x^n, whose second coefficient is 1/8.

import Mathlib
import Definitions.Def_QuantumMaxCutBFVProductRounding
open scoped BigOperators

namespace BFVBound

theorem bfv_cubic_sharp (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    (8 / (3 * Real.pi)) * s + (1 / (3 * Real.pi)) * s ^ 3 ≤ F s := by sorry

end BFVBound
