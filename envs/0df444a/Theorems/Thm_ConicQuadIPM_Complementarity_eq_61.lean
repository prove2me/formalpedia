-- Prove2me | Theorems.Thm_ConicQuadIPM_Complementarity_eq_61
-- name    : ConicQuadIPM.Complementarity.eq_61
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:51.881893+00:00
-- url     : https://prove2.me/theorems/e10b69f9-0daa-46bd-93d2-15af04cb6dda
-- title:
--   Appendix, (61), p. 36 — eᵀXSe = Σᵢ (Tⁱxⁱ)ᵀTⁱsⁱ = xᵀs
-- statement:
--   Let $K=K^1\times\dots\times K^k$ be as in §3, and for arbitrary $x,s$ (partitioned like $K$) put $X^i=\operatorname{mat}(T^ix^i)$ and $S^i=\operatorname{mat}(T^is^i)$, with $e^i$ the first unit vector of $\mathbb R^{n^i}$. Then for each $i$
--   $$
--   (e^i)^TX^iS^ie^i=(T^ix^i)^TT^is^i=(x^i)^Ts^i,
--   $$
--   and consequently
--   $$
--   e^TXSe=\sum_{i=1}^k (e^i)^TX^iS^ie^i=\sum_{i=1}^k (T^ix^i)^TT^is^i=x^Ts .
--   $$
--
--   This identity shows that any $x,s$ satisfying the arrow-head conditions (20) are complementary.
--
--   **Formalization Note.** No cone membership is needed. The block-diagonal matrices $X$, $S$ are represented by their blocks, so $e^TXSe$ is written as the sum over blocks. The printed upper limit $n$ of the first sum is a slip for $k$; the Lean sums over the $k$ blocks. Block dimensions (`WellFormed`) are assumed so that $T^iT^i=I$.
-- source:
--   Andersen, Roos & Terlaky, On implementing a primal-dual interior-point method for conic quadratic optimization, Math. Program. (2003); authors' preprint of 18 Dec 2000, Appendix, proof of Lemma 3.1, p. 36, (61)

import Mathlib
import Definitions.Def_ConicQuadIPM_Complementarity_Setting

open Matrix

namespace ConicQuadIPM.Complementarity

theorem eq_61 {k : ℕ} (kind : Fin k → ConeKind) (n : Fin k → ℕ)
    (hwf : WellFormed kind n) (x s : (i : Fin k) → Fin (n i) → ℝ) :
    (∀ i,
      e1 ⬝ᵥ ((arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1)
        = (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) ∧
      (Tmat (kind i) (n i) *ᵥ x i) ⬝ᵥ (Tmat (kind i) (n i) *ᵥ s i) = x i ⬝ᵥ s i) ∧
    ∑ i, e1 ⬝ᵥ ((arrow (Tmat (kind i) (n i) *ᵥ x i) * arrow (Tmat (kind i) (n i) *ᵥ s i)) *ᵥ e1)
      = ∑ i, x i ⬝ᵥ s i := by sorry

end ConicQuadIPM.Complementarity
