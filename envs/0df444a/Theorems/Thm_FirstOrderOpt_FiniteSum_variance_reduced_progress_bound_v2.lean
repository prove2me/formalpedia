-- Prove2me | Theorems.Thm_FirstOrderOpt_FiniteSum_variance_reduced_progress_bound_v2
-- name    : FirstOrderOpt.FiniteSum.variance_reduced_progress_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:16.250472+00:00
-- url     : https://prove2.me/theorems/0b2ce2fb-a524-4325-8575-46c994f34ecf
-- title:
--   Lemma 5.14 — one-step progress bound (5.3.10) (corrected: Bregman $V$)
-- statement:
--   Let $X$ be closed convex, $\nu$ a distance generating function on $X$ with prox-function $V$, $\Psi=f+h$ with $h$ convex and $f$ differentiable with $L$-Lipschitz gradient $\nabla f$ satisfying the generalized strong convexity (5.3.2) $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\mu V(x,y)$ on $X$ with $\mu\ge 0$. If $L\gamma\le\tfrac12$ and $x_{t+1}\in X$ minimizes $u\mapsto\gamma[\langle G_t,u\rangle+h(u)]+V(x_t,u)$ over $X$ (the update of Algorithm 5.6), then with $\delta_t=G_t-\nabla f(x_t)$, for every $x\in X$,
--   $$\gamma\big[\Psi(x_{t+1})-\Psi(x)\big]+V(x_{t+1},x)\le(1-\gamma\mu)V(x_t,x)+\gamma\langle\delta_t,x-x_t\rangle+\gamma^2\|\delta_t\|_*^2.$$
--
--   **Formalization Note.** The retired statement's free $V$ was constrained only through the step and (5.3.2), leaving $V(x_{t+1},x)$ unconstrained (disproved). The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. $\nabla f$ is the gradient of $f$ (`HasFDerivAt`), $h$ is convex and $X$ closed convex; the lemma holds for every $\mu\ge 0$ as in the book.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 280, Lemma 5.14, with (5.3.2) and (5.3.10)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.FiniteSum

open FirstOrderOpt.Prox

/-- Lemma 5.14 (one-step progress bound, Eq. (5.3.10)), Lan p. 280. Let `X` be closed convex, `ν`
a distance generating function on `X` with prox-function `V = ν.V`, `Ψ = f + h` with `h` convex
and `f` differentiable with `L`-Lipschitz gradient `∇f` satisfying the generalized strong
convexity (5.3.2) `f(y) ≥ f(x) + ⟨∇f(x), y - x⟩ + μ V(x, y)` with `μ ≥ 0`. If the stepsize
satisfies `Lγ ≤ 1/2` and `xt1` minimizes `u ↦ γ[⟨Gt, u⟩ + h(u)] + V(xt, u)` over `X` (the update
of Algorithm 5.6), then for every `x ∈ X`,
`γ[Ψ(xt1) - Ψ(x)] + V(xt1, x) ≤ (1 - γμ) V(xt, x) + γ⟨δt, x - xt⟩ + γ² ‖δt‖²_*`,
where `δt := Gt - ∇f(xt)`.

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
free `V` left `V(xt1, x)` unconstrained), `∇f` is the gradient of `f`, `h` is convex and `X` is
closed convex. The lemma holds for every `μ ≥ 0`, as in the book. -/
theorem variance_reduced_progress_bound_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f h Ψ : E → ℝ) (hΨ : ∀ x, Ψ x = f x + h x) (hhconv : ConvexOn ℝ X h)
    (gradf_full : E → E →L[ℝ] ℝ)
    (hgrad : ∀ x, HasFDerivAt f (gradf_full x) x)
    (L : ℝ) (hL : 0 < L) (hsmooth : ∀ x y, ‖gradf_full x - gradf_full y‖ ≤ L * ‖x - y‖)
    (μ : ℝ) (hμ : 0 ≤ μ)
    (hstrong : ∀ x ∈ X, ∀ y ∈ X, f y ≥ f x + (gradf_full x) (y - x) + μ * ν.V x y)
    (γ : ℝ) (hγ : 0 < γ) (hLγ : L * γ ≤ 1 / 2)
    (xt xt1 : E) (hxt : xt ∈ X) (hxt1 : xt1 ∈ X)
    (Gt δt : E →L[ℝ] ℝ) (hδt : δt = Gt - gradf_full xt)
    (hmin : ∀ y ∈ X, γ * (Gt xt1) + γ * h xt1 + ν.V xt xt1 ≤ γ * (Gt y) + γ * h y + ν.V xt y) :
    ∀ x ∈ X, γ * (Ψ xt1 - Ψ x) + ν.V xt1 x ≤
      (1 - γ * μ) * ν.V xt x + γ * (δt (x - xt)) + γ ^ 2 * ‖δt‖ ^ 2 := by sorry

end FirstOrderOpt.FiniteSum
