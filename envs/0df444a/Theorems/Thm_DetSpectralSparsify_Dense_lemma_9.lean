-- Prove2me | Theorems.Thm_DetSpectralSparsify_Dense_lemma_9
-- name    : DetSpectralSparsify.Dense.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:00:39.853389+00:00
-- url     : https://prove2.me/theorems/c7beb0d0-619a-4c4b-8400-80eb6224c851
-- title:
--   Lemma 9 (Approximation to the exponential) — a computable polynomial of degree O(√(R log 1/τ) + log 1/τ) within τ of e^{−A}
-- statement:
--   There are an absolute constant $C$ and a program which, given reals $R\ge0$ and $0<\tau<1$, computes a polynomial $p$ of degree
--   $$\deg p\;\le\;C\Big(\sqrt{R\log\tfrac1\tau}+\log\tfrac1\tau\Big)$$
--   such that for every real symmetric matrix $A$ (of any dimension) with $0\preceq A\preceq RI$,
--   $$e^{-A}-\tau I\;\preceq\;p(A)\;\preceq\;e^{-A}+\tau I .$$
--
--   The polynomials approximate the matrix exponentials $e^{-Q_{\pm,j}}$ in the sparse score implementation. The paper cites [SV14, Theorem 4.1].
--
--   **Formalization Note** The program runs on the real RAM of `Machine` with input $(R,\tau)$ in real cells $0,1$ and outputs $D$ in natural cell $0$ and the monomial coefficients of $p$ in real cells $0,\dots,D$; the degree bound is stated for $D$.
--
--   Differences from the source:
--   - reading: one can compute a polynomial p → a fixed real-RAM program halts on (R, τ) with the coefficients of p (no running-time bound); reason: the source asserts computability and states no cost
--   - reading: whenever 0 ⪯ A ⪯ RI and 0 < τ < 1, one can compute a polynomial p … satisfying e^{−A} − τI ⪯ p(A) ⪯ e^{−A} + τI → p is computed from (R, τ) alone and the bound holds for every real symmetric A of every dimension with 0 ⪯ A ⪯ RI; reason: the next sentence of the source ('the corresponding matrix guarantees for scalar approximation follow immediately by applying the polynomials to the eigenvalues') shows p is a scalar approximation on [0, R]; this is the stronger reading
--   - encoding: deg p = O(√(R log(1/τ)) + log(1/τ)) → the output length index D satisfies D ≤ C(√(R log(1/τ)) + log(1/τ)) with C absolute, so deg p ≤ D; reason: the O-constant is absolute
-- source:
--   Trevor Vaughn, Jason Li, Deterministic Spectral Sparsification in Almost-Linear Time for Dense Graphs, STOC 2027 submission #370 (October 2026), source.pdf SHA-256 b88d92728f937730b7e9664f482778048c0b667d4376e0488686c9708e5d8467, p.15, Lemma 9 (citing Sachdeva–Vishnoi 2014, Theorem 4.1)

import Definitions.Def_DetSpectralSparsify_Dense_Machine

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

/-- Lemma 9 (Approximation to the exponential), p.15 ([SV14, Theorem 4.1]). There are an absolute
`C` and a program that, given `R ≥ 0` and `0 < τ < 1`, computes the coefficients of a polynomial
`p` of degree `≤ C (√(R log(1/τ)) + log(1/τ))` with `e^{-A} - τ I ⪯ p(A) ⪯ e^{-A} + τ I` for every
symmetric `A` with `0 ⪯ A ⪯ R I`, of any dimension. -/
theorem lemma_9 :
    ∃ (C : ℝ) (P : Program) (K : ℕ), 0 < C ∧ ∀ R τ : ℝ, 0 ≤ R → 0 < τ → τ < 1 →
      ∃ (T : ℕ) (s' : State), RunsWithin P K 2 (paramInput [] [R, τ]) T s' ∧
        (s'.nat 0 : ℝ) ≤ C * (Real.sqrt (R * Real.log (1 / τ)) + Real.log (1 / τ)) ∧
        ∀ (r : ℕ) (A : Matrix (Fin r) (Fin r) ℝ), A.PosSemidef → PSDLe A (R • 1) →
          PSDLe (NormedSpace.exp (-A) - τ • 1) (Polynomial.aeval A (decodePoly s')) ∧
          PSDLe (Polynomial.aeval A (decodePoly s')) (NormedSpace.exp (-A) + τ • 1) := by sorry

end DetSpectralSparsify.Dense
