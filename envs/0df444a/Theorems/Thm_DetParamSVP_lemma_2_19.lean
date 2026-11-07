-- Prove2me | Theorems.Thm_DetParamSVP_lemma_2_19
-- name    : DetParamSVP.lemma_2_19
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:49:47.058955+00:00
-- url     : https://prove2.me/theorems/85de02c8-a096-4938-b809-62418905cd5e
-- title:
--   Lemma 2.19 — a common zero of $f_1,\dots,f_{n-1}$ where $f_n\ne0$, near a nonsingular solution over $\mathbb F_Q$
-- statement:
--   Let $K=\mathbb F_Q$, let $n\ge2$, and let $f_1,\dots,f_n\in K[X_1,\dots,X_n]$ be nonconstant polynomials with
--
--   $$\Delta=\prod_{i=1}^{n-1}\deg f_i .$$
--
--   Suppose that $\xi\in K^n$ satisfies $f_1(\xi)=\dots=f_n(\xi)=0$ and that the Jacobian matrix $\big(\tfrac{\partial f_i}{\partial X_j}(\xi)\big)_{i,j\in[n]}$ is invertible. If $Q>9\Delta^5$ and $Q>9\Delta\deg f_n$, then there is $x\in K^n$ with
--
--   $$f_1(x)=\dots=f_{n-1}(x)=0,\qquad f_n(x)\ne0.$$
--
--   The lemma replaces the implicit function theorem over finite fields; it supplies the point that completes the construction of the locally dense lattice in Theorem 3.4.
--
--   **Formalization Note** $\deg$ is the total degree, and partial derivatives are formal.
--
--   Differences from the source:
--   - encoding: n ≥ 2 polynomials f₁, …, f_n in n variables, f_n distinguished → n + 1 polynomials in n + 1 variables indexed by Fin (n + 1), n ≥ 1, the distinguished one indexed by Fin.last n; reason: reindexing
--   - encoding: K = F_Q → any finite field K, with Q = Fintype.card K; reason: all fields with Q elements are isomorphic
--   - encoding: nonconstant; Jacobian invertible → 0 < totalDegree; determinant of the Jacobian nonzero; reason: equivalent over a field
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 2.19, p.16

import Mathlib

set_option autoImplicit false

namespace DetParamSVP

open MvPolynomial

/-- **Lemma 2.19** (rational points near a nonsingular solution). Let `K = F_Q`, `n ≥ 2`, and let
`f₁, …, f_n ∈ K[X₁, …, X_n]` be nonconstant with `Δ = ∏_{i=1}^{n−1} deg f_i`. Suppose `ξ ∈ K^n`
satisfies `f₁(ξ) = ⋯ = f_n(ξ) = 0` and the Jacobian matrix of `f₁, …, f_n` at `ξ` is invertible.
If `Q > 9Δ^5` and `Q > 9Δ deg f_n`, then some `x ∈ K^n` has `f₁(x) = ⋯ = f_{n−1}(x) = 0` and
`f_n(x) ≠ 0`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 2.19, p.16.

**Formalization Note.** The paper's `n ≥ 2` polynomials in `n` variables are `n + 1` polynomials
`f : Fin (n + 1) → K[X_0, …, X_n]` with `n ≥ 1`; the distinguished `f_n` is `f (Fin.last n)`.
`K` is any finite field and `Q = Fintype.card K` (all fields with `Q` elements are isomorphic).
`deg` is `totalDegree`, and "nonconstant" is `0 < totalDegree`. The Jacobian is the
`(n+1) × (n+1)` matrix `(∂f_i/∂X_j(ξ))`, invertible iff its determinant is nonzero. -/
theorem lemma_2_19 {K : Type*} [Field K] [Fintype K] (n : ℕ) (hn : 1 ≤ n)
    (f : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) (hf : ∀ i, 0 < (f i).totalDegree)
    (ξ : Fin (n + 1) → K) (hξ : ∀ i, eval ξ (f i) = 0)
    (hJ : (Matrix.of fun i j => eval ξ (pderiv j (f i))).det ≠ 0)
    (hQ₁ : 9 * (∏ i : Fin n, (f i.castSucc).totalDegree) ^ 5 < Fintype.card K)
    (hQ₂ : 9 * (∏ i : Fin n, (f i.castSucc).totalDegree) * (f (Fin.last n)).totalDegree <
      Fintype.card K) :
    ∃ x : Fin (n + 1) → K, (∀ i : Fin n, eval x (f i.castSucc) = 0) ∧
      eval x (f (Fin.last n)) ≠ 0 := by sorry

end DetParamSVP
