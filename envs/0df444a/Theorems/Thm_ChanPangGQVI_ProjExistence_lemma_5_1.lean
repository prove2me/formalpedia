-- Prove2me | Theorems.Thm_ChanPangGQVI_ProjExistence_lemma_5_1
-- name    : ChanPangGQVI.ProjExistence.lemma_5_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T12:43:12.465855+00:00
-- url     : https://prove2.me/theorems/dfc968b4-b01f-4ffe-acce-83bb2775aa79
-- title:
--   Lemma 5.1 — continuity of the projection p(x, y) = P_{K(x)}(y) at (x₀, y₀)
-- statement:
--   Let $K$ be a point-to-set mapping of $\mathbb R^n$ into itself such that $K(x)$ is a nonempty, closed and convex set for every $x$, and suppose that $K$ is **continuous at the point** $x_0$: it is upper semicontinuous at $x_0$ (for every open set $G\supseteq K(x_0)$ there is a neighbourhood $N$ of $x_0$ with $K(x)\subseteq G$ for all $x\in N$) and lower semicontinuous at $x_0$ (for every open set $G$ meeting $K(x_0)$ there is a neighbourhood $N$ of $x_0$ with $K(x)$ meeting $G$ for all $x\in N$). Let
--
--   $$
--   p(x,y)=P_{K(x)}(y)
--   $$
--
--   be the projection of $y$ on $K(x)$ in the Euclidean norm. Then for every $y_0\in\mathbb R^n$ the function $p$ is continuous at the point $(x_0,y_0)$ of $\mathbb R^n\times\mathbb R^n$.
--
--   The lemma is what makes the map $x\mapsto P_{K(x)}(x-f(x))$ continuous, so that the Brouwer fixed point theorem applies to it in the proof of Theorem 5.2.
--
--   **Formalization Note** Upper and lower semicontinuity at a point are Mathlib's `UpperHemicontinuousAt` and `LowerHemicontinuousAt`, with full neighbourhoods of $x_0$ in $\mathbb R^n$. The hypothesis that every $K(x)$ is nonempty is implicit in the paper, whose projection function $p(x,y)=P_{K(x)}(y)$ is defined only for nonempty $K(x)$; it is stated explicitly here, so the junk value of `proj` never enters.
-- source:
--   Chan and Pang, The generalized quasi-variational inequality problem, Math. Oper. Res. 7 (1982), p. 220, Lemma 5.1

import Mathlib
import Definitions.Def_ChanPangGQVI_Shared_Projection

namespace ChanPangGQVI.ProjExistence

/-- **Lemma 5.1** (Chan and Pang 1982, p. 220). Suppose that the point-to-set mapping `K` is
continuous (upper and lower semicontinuous, with full neighbourhoods in `ℝⁿ`) at the point `x₀`
and that `K(x)` is a closed and convex set for all `x`. Then for each `y₀` the projection function
`p(x, y) = P_{K(x)}(y)` is continuous at `(x₀, y₀)`.

Implicit hypothesis made explicit: `K(x)` is nonempty for all `x`. The paper's projection
function `p(x, y) = P_{K(x)}(y)` is only defined when `K(x) ≠ ∅`, and its proof picks points
`zᵏ ∈ K(xᵏ)`. -/
theorem lemma_5_1 {n : ℕ}
    (K : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hK_upper : UpperHemicontinuousAt K x₀) (hK_lower : LowerHemicontinuousAt K x₀)
    (hK_closed : ∀ x, IsClosed (K x)) (hK_convex : ∀ x, Convex ℝ (K x))
    (hK_nonempty : ∀ x, (K x).Nonempty)
    (y₀ : EuclideanSpace ℝ (Fin n)) :
    ContinuousAt
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        ChanPangGQVI.Shared.proj (K p.1) p.2)
      (x₀, y₀) := by sorry

end ChanPangGQVI.ProjExistence
