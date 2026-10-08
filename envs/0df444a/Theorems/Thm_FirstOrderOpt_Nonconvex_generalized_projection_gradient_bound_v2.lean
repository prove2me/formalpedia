-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_generalized_projection_gradient_bound_v2
-- name    : FirstOrderOpt.Nonconvex.generalized_projection_gradient_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:16.337445+00:00
-- url     : https://prove2.me/theorems/294d196e-6ade-4654-8e5f-885a5fe670bf
-- title:
--   Lemma 6.4 — inner-product bound for the generalized projected gradient (corrected)
-- statement:
--   Let $X$ be closed convex in a real inner-product space, $h$ convex on $X$, $\nu$ a distance generating function on $X$ with prox-function $V$ (so $V(x,u)\ge\tfrac12\|u-x\|^2$), $x\in X$, $g$ a vector and $\gamma>0$. Let $x^+\in X$ be the generalized projection (6.2.6), the minimizer over $X$ of $u\mapsto\langle g,u\rangle+\tfrac1\gamma V(x,u)+h(u)$, and $P_X(x,g,\gamma):=\tfrac1\gamma(x-x^+)$ the generalized projected gradient (6.2.7). Then
--   $$\langle g,P_X(x,g,\gamma)\rangle\ge\|P_X(x,g,\gamma)\|^2+\tfrac1\gamma\big[h(x^+)-h(x)\big].$$
--
--   **Formalization Note.** The retired statement had no hypothesis on $V$ or $h$ at all (disproved). The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. The proof needs the strong-convexity lower bound $V(x,u)\ge\tfrac12\|u-x\|^2$ (a consequence of the definition) and the convexity of $h$; closed convexity of $X$ is the standing assumption.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 328, Lemma 6.4

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace
open FirstOrderOpt.Prox

/-- Lemma 6.4, Lan p. 328. Let `X` be closed convex, `h` convex on `X`, `ν` a distance
generating function on `X` with prox-function `V = ν.V` (so `V(x, u) ≥ ½‖u - x‖²`), and let
`xPlus` be the generalized projection (6.2.6) `argmin_{u ∈ X} ⟨g, u⟩ + (1/γ)V(x, u) + h(u)` for
`x ∈ X`, `γ > 0`. With `P_X(x, g, γ) := (1/γ)(x - xPlus)` the generalized projected gradient
(6.2.7), `⟨g, P_X(x, g, γ)⟩ ≥ ‖P_X(x, g, γ)‖² + (1/γ)[h(xPlus) - h(x)]`.

Corrected version: `V` is the Bregman distance of a distance generating function and `h` is
convex, `X` closed convex (the retired statement had no hypothesis on `V` or `h` at all; the proof
needs the strong-convexity lower bound of `V` and the convexity of `h`). -/
theorem generalized_projection_gradient_bound_v2 {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (h : E → ℝ) (hhconv : ConvexOn ℝ X h)
    (ν : DistanceGeneratingFunction X)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * ν.V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * ν.V x u + h u)
    (PXval : E) (hPX : PXval = (1 / γ) • (x - xPlus)) :
    ⟪g, PXval⟫ ≥ ‖PXval‖ ^ 2 + (1 / γ) * (h xPlus - h x) := by sorry

end FirstOrderOpt.Nonconvex
