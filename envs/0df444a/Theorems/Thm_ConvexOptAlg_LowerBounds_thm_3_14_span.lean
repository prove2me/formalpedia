-- Prove2me | Theorems.Thm_ConvexOptAlg_LowerBounds_thm_3_14_span
-- name    : ConvexOptAlg.LowerBounds.thm_3_14_span
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T17:44:21.396644+00:00
-- url     : https://prove2.me/theorems/a2ce3036-fee6-49b4-8234-0eee3d00742c
-- title:
--   Proof of Theorem 3.14, p. 282 — under (3.15) the query x_s lies in Span(e₁, …, e_{s−1}), so f(x_s) = f_s(x_s)
-- statement:
--   Let $\beta>0$, $2t+1\le n$, and $f=f_{2t+1}$, where $f_k(x)=\frac\beta8x^\top A_kx-\frac\beta4x^\top e_1$. Let $g$ be the gradient of $f$ and let $(x_s)_{s\ge1}$ be the queries of a black-box procedure satisfying (3.15) for the gradient oracle $g$. Then for every $s\ge1$
--   $$x_s\in\mathrm{Span}(e_1,\dots,e_{s-1}).$$
--   In particular, for $1\le s\le t$, $x_s(i)=0$ for $i=s,\dots,n$, hence
--   $$x_s^\top A_{2t+1}x_s=x_s^\top A_sx_s\qquad\text{and}\qquad f(x_s)=f_s(x_s).$$
--
--   This is where the tridiagonal structure of the hard instance meets the span assumption: every query reveals at most one new coordinate, so after $t$ steps the method only sees the smaller problem $f_s$.
--
--   **Formalization Note** Coordinates and basis vectors are 1-based as in the book (`coord`, `basisVec`). The gradient map $g$ is any map with $\nabla f(y)=g(y)$ for every $y$, so it is the gradient.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 282

import Mathlib
import Definitions.Def_ConvexOptAlg_LowerBounds_Defs

open scoped InnerProductSpace

namespace ConvexOptAlg.LowerBounds

/-- Bubeck, arXiv:1405.4980v2, proof of Theorem 3.14, p. 282 (the span claim). Let
`f = f_{2t+1}`, `f(x) = (β/8) xᵀA_{2t+1}x − (β/4) xᵀe₁`, with gradient map `g`, and let the query
sequence `x` satisfy (3.15) for the oracle `g`. Then for every `s ≥ 1`, `x_s` lies in the linear
span of `e₁, …, e_{s−1}` (book indices). In particular for `1 ≤ s ≤ t`, `x_s(i) = 0` for
`i = s, …, n`, hence `x_sᵀA_{2t+1}x_s = x_sᵀA_s x_s` and `f(x_s) = f_s(x_s)`. -/
theorem thm_3_14_span (n t : ℕ) (β : ℝ) (hβ : 0 < β) (htn : 2 * t + 1 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hg : ∀ y, HasGradientAt (fK n β (2 * t + 1)) (g y) y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hx : SatisfiesSpanCondition g x) :
    (∀ s : ℕ, 1 ≤ s → x s ∈ Submodule.span ℝ (basisVec n '' Set.Ico 1 s)) ∧
      ∀ s : ℕ, 1 ≤ s → s ≤ t →
        (∀ i ∈ Finset.Icc s n, coord (x s) i = 0) ∧
          quadForm (tridiag n (2 * t + 1)) (x s) = quadForm (tridiag n s) (x s) ∧
          fK n β (2 * t + 1) (x s) = fK n β s (x s) := by sorry

end ConvexOptAlg.LowerBounds
