-- Prove2me | Theorems.Thm_FirstOrderOpt_Stochastic_stochastic_mirror_iterate_three_point_v2
-- name    : FirstOrderOpt.Stochastic.stochastic_mirror_iterate_three_point_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:36.685364+00:00
-- url     : https://prove2.me/theorems/57c1ff69-e135-4633-a6ad-c74593d13f8d
-- title:
--   Lemma 3.4 for the stochastic mirror-descent step (corrected: Bregman $V$, convex $X$)
-- statement:
--   Let $X$ be a closed convex subset of a normed space, $\nu$ a distance generating function on $X$ with prox-function $V$, $x_t\in X$, $G_t$ a continuous linear functional (the stochastic subgradient of step $t$) and $\gamma_t\in\mathbb R$. If $x_{t+1}\in X$ minimizes $u\mapsto\gamma_tG_t(u)+V(x_t,u)$ over $X$ (the stochastic mirror-descent update (4.1.6)), then for every $x\in X$
--   $$\gamma_tG_t(x_{t+1}-x)+V(x_t,x_{t+1})\le V(x_t,x)-V(x_{t+1},x).$$
--   This is Lemma 3.4 with $g_t$ replaced by $G_t$, as invoked on p. 115.
--
--   **Formalization Note.** The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. Closed convexity of $X$ and $x_t\in X$ are stated; the retired statement had neither, and with a free $V$ argmin-minimality does not imply the three-point inequality (disproved).
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 60, Lemma 3.4, as invoked for the stochastic update on p. 115

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Stochastic

open FirstOrderOpt.Prox

/-- Lemma 3.4 (three-point inequality), Lan p. 60, restated for the stochastic mirror-descent
update as invoked on p. 115 ("the result in Lemma 3.4 holds with `gt` replaced by `Gt`"). Let `X`
be closed convex, `ν` a distance generating function on `X` with prox-function `V = ν.V`, and let
`xt1` minimize `u ↦ γt·Gt(u) + V(xt, u)` over `X` (the stochastic update (4.1.6)) for `xt ∈ X` and a
stochastic (sub)gradient functional `Gt`. Then for every `x ∈ X`,
`γt·Gt(xt1 - x) + V(xt, xt1) ≤ V(xt, x) - V(xt1, x)`.

Corrected version: `V` is the Bregman distance of a distance generating function and `X` is
closed convex; the retired statement left `V` a free function, for which argmin-minimality does
not imply the three-point inequality. -/
theorem stochastic_mirror_iterate_three_point_v2 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (xt xt1 : E) (Gt : E →L[ℝ] ℝ) (γt : ℝ)
    (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (hmin : ∀ x ∈ X, γt * Gt xt1 + ν.V xt xt1 ≤ γt * Gt x + ν.V xt x) :
    ∀ x ∈ X, γt * Gt (xt1 - x) + ν.V xt xt1 ≤ ν.V xt x - ν.V xt1 x := by sorry

end FirstOrderOpt.Stochastic
