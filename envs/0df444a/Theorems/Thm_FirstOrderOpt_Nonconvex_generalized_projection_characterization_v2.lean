-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_generalized_projection_characterization_v2
-- name    : FirstOrderOpt.Nonconvex.generalized_projection_characterization_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:06.291654+00:00
-- url     : https://prove2.me/theorems/dd3e8abe-003a-41c7-aed5-050afbcb0ad6
-- title:
--   Lemma 6.6 — characterization of the generalized projection (corrected: Bregman $V$, convex $h$)
-- statement:
--   Let $X$ be closed convex in a real inner-product space, $h$ convex on $X$, $\nu$ a distance generating function on $X$ with prox-function $V$, $x\in X$, $g$ a vector and $\gamma>0$. If $x^+\in X$ is the generalized projection (6.2.6), the minimizer over $X$ of $u\mapsto\langle g,u\rangle+\tfrac1\gamma V(x,u)+h(u)$, then for every $u\in X$
--   $$\langle g,x^+\rangle+h(x^+)+\tfrac1\gamma V(x,x^+)\le\langle g,u\rangle+h(u)+\tfrac1\gamma\big[V(x,u)-V(x^+,u)\big].$$
--
--   **Formalization Note.** The retired statement had a completely free $V$ (not even $V(u,u)=0$), so the extra term $V(x^+,u)$ was unconstrained (disproved). The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. Convexity of $h$ and closed convexity of $X$ are the standing assumptions needed for the first-order optimality condition of the composite step.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 329, Lemma 6.6 (a special case of Lemma 3.5)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

/-- Lemma 6.6, Lan p. 329 (a special case of Lemma 3.5). Let `X` be closed convex, `h` convex on
`X`, `ν` a distance generating function on `X` with prox-function `V = ν.V`, and let `xPlus` be the
generalized projection (6.2.6) `argmin_{u ∈ X} ⟨g, u⟩ + (1/γ)V(x, u) + h(u)` for `x ∈ X`, `γ > 0`.
Then for every `u ∈ X`,
`⟨g, xPlus⟩ + h(xPlus) + (1/γ)V(x, xPlus) ≤ ⟨g, u⟩ + h(u) + (1/γ)[V(x, u) - V(xPlus, u)]`.

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
statement left `V` entirely free, so the extra term `V(xPlus, u)` was unconstrained), and the
standing assumptions `X` closed convex and `h` convex are stated. -/
theorem generalized_projection_characterization_v2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * ν.V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * ν.V x u + h u) :
    ∀ u ∈ X, ⟪g, xPlus⟫ + h xPlus + (1 / γ) * ν.V x xPlus ≤
      ⟪g, u⟫ + h u + (1 / γ) * (ν.V x u - ν.V xPlus u) := by sorry

end FirstOrderOpt.Nonconvex
