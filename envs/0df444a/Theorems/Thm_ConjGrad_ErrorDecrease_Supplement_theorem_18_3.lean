-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_18_3
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_18_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:06:27.129361+00:00
-- url     : https://prove2.me/theorems/9f37f6b5-7bab-4760-85c7-d86e94b8b534
-- title:
--   Theorem 18:3 — any positive $a_0,\dots,a_{n-1}$, $b_0,\dots,b_{n-1}$ are cg numbers of some $A$, $r_0$
-- statement:
--   Given positive numbers $a_0,\dots,a_{n-1}$ and $b_0,\dots,b_{n-1}$, there are a real symmetric positive definite matrix $A$ (of order $n+1$) and an initial residual $r_0=k-Ax_0$ such that the cg-algorithm applied to $A$, $r_0$ yields the given numbers as its first $n$ step lengths $a_i=|r_i|^2/(p_i,Ap_i)$ and coefficients $b_i=|r_{i+1}|^2/|r_i|^2$.
--
--   There is no restriction whatever on the positive cg constants; in particular the residual lengths can behave arbitrarily, although the error vector always decreases (Theorem 6:3).
--
--   **Formalization Note** The cg-algorithm is the published iteration `cgIter`; $a_i$ is `cgAlpha` and $b_i$ is `cgBeta`. The initial residual is given through $k$ and $x_0$.
--
--   Differences from the source:
--   - reading: “a symmetric positive definite matrix $A$” (order not fixed in the statement) → a matrix of order $n+1$; reason: a cg run in dimension $n$ ends with $r_n=0$, hence $b_{n-1}=0$, so a prescribed $b_{n-1}>0$ needs order at least $n+1$; order $n+1$ realizes all $2n$ prescribed numbers
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 432, Theorem 18:3 (PDF p. 24)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_cgIter
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_smoothed

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 18:3 (Hestenes–Stiefel 1952, p. 432): any positive numbers `a₀, …, aₙ₋₁` and
`b₀, …, bₙ₋₁` are the first `n` step lengths and coefficients of the cg-algorithm for some
symmetric positive definite matrix `A` (here of order `n + 1`) and initial residual. -/
theorem theorem_18_3 (n : ℕ) (a b : ℕ → ℝ) (ha : ∀ i < n, 0 < a i) (hb : ∀ i < n, 0 < b i) :
    ∃ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ, A.PosDef ∧ ∃ k x₀ : Fin (n + 1) → ℝ,
      ∀ i < n, cgAlpha A (cgIter A k x₀ i) = a i ∧ cgBeta A k x₀ i = b i := by sorry

end ConjGrad.ErrorDecrease.Supplement
