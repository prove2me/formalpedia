-- Prove2me | Theorems.Thm_FirstOrderOpt_Stochastic_stochastic_mirror_descent_bound_v2
-- name    : FirstOrderOpt.Stochastic.stochastic_mirror_descent_bound_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:17:37.65723+00:00
-- url     : https://prove2.me/theorems/c60c80d7-4c31-43c2-8e4e-c77c544b8433
-- title:
--   Theorem 4.1 — stochastic mirror descent expected bound (corrected: convex $f$, Bregman $V$, conditional oracle)
-- statement:
--   Consider $\min_{x\in X}f(x)$ with $X$ closed convex in a normed space and $f$ convex on $X$, and let $\nu$ be a distance generating function on $X$ with prox-function $V$. On a probability space with a filtration $(\mathcal G_t)$ (the history $\xi_{[t]}$), let the random iterates $x_t\in X$ of stochastic mirror descent (4.1.6) be $\mathcal G_t$-measurable, $x_{t+1}=\arg\min_{u\in X}\{\gamma_tG_t(u)+V(x_t,u)\}$ pointwise, where the stochastic subgradient $G_t$ is $\mathcal G_{t+1}$-measurable and satisfies (4.1.7) conditionally on the history: $\mathbb E[G_t\mid\mathcal G_t]=g(x_t)$ for a subgradient selector $g$ of $f$ on $X$ with $\|g(x)\|_*\le M$, and $\mathbb E[\|G_t-g(x_t)\|_*^2\mid\mathcal G_t]\le\sigma^2$. If $x^*$ is an optimal solution and $\bar x_s^k$ the weighted average (3.1.9), then
--   $$\mathbb E\big[f(\bar x_s^k)\big]-f(x^*)\le\Big(\sum_{t=s}^k\gamma_t\Big)^{-1}\Big(\mathbb E\,V(x_s,x^*)+(M^2+\sigma^2)\sum_{t=s}^k\gamma_t^2\Big).$$
--
--   **Formalization Note.** The retired statement assumed the subgradient inequality only at the iterates (no convexity of $f$, so Jensen at $\bar x$ failed — the accepted disproof), took $V$ as a free function, and replaced the oracle's conditional unbiasedness by a plain expectation identity $\mathbb E\langle\delta_t,x_t-x^*\rangle=0$. The corrected statement has $f$ convex on $X$, the retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. The oracle assumptions are stated conditionally on the history filtration, as in the book; integrability guards keep the Bochner integrals from defaulting to $0$. The expectations of $f(\bar x)$ and $V(x_s,x^*)$ are assumed finite, as the book implicitly does.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 113, Theorem 4.1, with (4.1.6)-(4.1.7)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Stochastic

open MeasureTheory FirstOrderOpt.Prox

/-- Theorem 4.1 (stochastic mirror descent, expected convergence bound), Lan p. 113. For
`min_{x ∈ X} f(x)` with `X` closed convex and `f` convex on `X`, let `ν` be a distance generating
function on `X` with prox-function `V = ν.V`, and let `x t : Ω → E` be the random iterates of
stochastic mirror descent (4.1.6): `x (t+1)` minimizes `u ↦ γt·(G t)(u) + V(x t, u)` over `X`,
where `G t` is a stochastic subgradient at `x t`. The randomness is modelled by a filtration
`𝒢` (the history `ξ[t]`): `x t` is `𝒢 t`-measurable, `G t` is `𝒢 (t+1)`-measurable, and (4.1.7)
holds conditionally on the history: `E[G t | 𝒢 t] = g(x t)` for a subgradient selector `g` of
`f` with `‖g(x)‖_* ≤ M` on `X`, and `E[‖G t - g(x t)‖²_* | 𝒢 t] ≤ σ²`. If `xstar` is an optimal
solution and `xbar` the weighted average `x̄ᵏₛ` of (3.1.9), then
`E[f(x̄ᵏₛ)] - f* ≤ (Σ_{t=s}^k γt)⁻¹ (E[V(x s, x*)] + (M² + σ²) Σ_{t=s}^k γt²)`.

Corrected version: `f` is convex on `X` (the retired statement only assumed the subgradient
inequality at the iterates, so Jensen at the averaged point was unavailable), `V` is the Bregman
distance of a distance generating function, `X` is closed convex, and the stochastic oracle's
unbiasedness and variance bound are stated conditionally on the history filtration, as in the
book, instead of as a plain expectation identity. -/
theorem stochastic_mirror_descent_bound_v2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝒢 : Filtration ℕ m0)
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (f : E → ℝ) (hfconv : ConvexOn ℝ X f)
    (ν : DistanceGeneratingFunction X) (M σ : ℝ) (hM : 0 < M) (hσ : 0 < σ)
    (x : ℕ → Ω → E) (G : ℕ → Ω → E →L[ℝ] ℝ) (g : E → E →L[ℝ] ℝ) (γ : ℕ → ℝ)
    (hx : ∀ t ω, x t ω ∈ X) (hγ : ∀ t, 0 < γ t)
    (hxMeas : ∀ t, StronglyMeasurable[𝒢 t] (x t))
    (hGMeas : ∀ t, StronglyMeasurable[𝒢 (t + 1)] (G t))
    (hsub : ∀ x' ∈ X, ∀ y ∈ X, f x' + (g x') (y - x') ≤ f y)
    (hgnorm : ∀ x' ∈ X, ‖g x'‖ ≤ M)
    (hGint : ∀ t, Integrable (fun ω => G t ω - g (x t ω)) P)
    (hunbiased : ∀ t, condExp (𝒢 t) P (fun ω => G t ω - g (x t ω)) =ᵐ[P] 0)
    (hintsecmom : ∀ t, Integrable (fun ω => ‖G t ω - g (x t ω)‖ ^ 2) P)
    (hsecmom : ∀ t, condExp (𝒢 t) P (fun ω => ‖G t ω - g (x t ω)‖ ^ 2) ≤ᵐ[P]
      (fun _ => σ ^ 2))
    (hmin : ∀ t ω, ∀ y ∈ X, γ t * (G t ω) (x (t + 1) ω) + ν.V (x t ω) (x (t + 1) ω) ≤
      γ t * (G t ω) y + ν.V (x t ω) y)
    (xstar : E) (hxstar : xstar ∈ X) (hxstar_opt : ∀ y ∈ X, f xstar ≤ f y)
    (s k : ℕ) (hsk : s ≤ k)
    (xbar : Ω → E)
    (hxbar : ∀ ω, xbar ω = (∑ t ∈ Finset.Icc s k, γ t)⁻¹ • ∑ t ∈ Finset.Icc s k, γ t • x t ω)
    (hintf : Integrable (fun ω => f (xbar ω)) P)
    (hintV : Integrable (fun ω => ν.V (x s ω) xstar) P) :
    ∫ ω, f (xbar ω) ∂P - f xstar ≤ (∑ t ∈ Finset.Icc s k, γ t)⁻¹ *
      (∫ ω, ν.V (x s ω) xstar ∂P + (M ^ 2 + σ ^ 2) * ∑ t ∈ Finset.Icc s k, (γ t) ^ 2) := by sorry

end FirstOrderOpt.Stochastic
