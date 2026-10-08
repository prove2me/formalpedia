-- Prove2me | Theorems.Thm_ConicQuadIPM_NewtonStep_eq_61
-- name    : ConicQuadIPM.NewtonStep.eq_61
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T03:09:35.260702+00:00
-- url     : https://prove2.me/theorems/6a473ff7-1c86-4796-8107-85aad6fda292
-- title:
--   (61), Appendix, proof of Lemma 3.1, p. 36 — eᵀXSe = Σᵢ (Tⁱxⁱ)ᵀTⁱsⁱ = xᵀs
-- statement:
--   Let $K = K^1\times\cdots\times K^k$ be a product of cones of the kinds $\mathbb R_+$, $K^q$, $K^r$, with $n^i = 1$ for $\mathbb R_+$, $n^i\ge1$ for $K^q$ and $n^i\ge2$ for $K^r$, and let $T^i$ be the matrices of Definition 3.2. For arbitrary vectors $x = (x^1;\dots;x^k)$ and $s = (s^1;\dots;s^k)$ put $X^i = \operatorname{mat}(T^ix^i)$, $S^i = \operatorname{mat}(T^is^i)$, and let $e^i$ be the first unit vector of $\mathbb R^{n^i}$. Then
--   $$
--   e^TXSe = \sum_{i=1}^k (e^i)^TX^iS^ie^i = \sum_{i=1}^k (T^ix^i)^TT^is^i = x^Ts.
--   $$
--
--   This identity turns the arrow-head complementarity products into the duality gap. In the proof of Lemma 4.1 it evaluates $e^TX^{(0)}S^{(0)}e = (x^{(0)})^Ts^{(0)}$; in the proof of Lemma 3.1 it shows that $X^iS^ie^i = 0$ for all $i$ implies $x^Ts = 0$.
--
--   **Formalization Note** The left-hand side is written block by block, $\sum_i (e^i)^TX^iS^ie^i$, which is $e^TXSe$ for the block-diagonal $X$, $S$. The page prints the upper limit of the first sum as $n$; it is $k$. The statement is the chain of the last two equalities. No cone membership is assumed, as on the page; the dimension conventions are needed (for $K^r$ with $n^i = 1$ the matrix $T^i$ is not orthogonal).
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, p. 36, Appendix, proof of Lemma 3.1, (61)

import Mathlib
import Definitions.Def_ConicQuadIPM_NewtonStep_Setting

namespace ConicQuadIPM.NewtonStep

open Matrix

theorem eq_61
    {k : ℕ} (kind : Fin k → ConicQuadIPM.Complementarity.ConeKind) (n : Fin k → ℕ) (hwf : ConicQuadIPM.Complementarity.WellFormed kind n)
    (x s : (i : Fin k) → Fin (n i) → ℝ) :
    (∑ i, ConicQuadIPM.Complementarity.e1 ⬝ᵥ ((ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) * ConicQuadIPM.Complementarity.arrow (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i))
        *ᵥ ConicQuadIPM.Complementarity.e1))
      = ∑ i, (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i) ∧
    (∑ i, (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (ConicQuadIPM.Complementarity.Tmat (kind i) (n i) *ᵥ s i))
      = ∑ i, x i ⬝ᵥ s i := by sorry

end ConicQuadIPM.NewtonStep
