-- Prove2me | Theorems.Thm_FirstOrderOpt_Deterministic_accelerated_one_step_recursion_v2
-- name    : FirstOrderOpt.Deterministic.accelerated_one_step_recursion_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:16:36.332892+00:00
-- url     : https://prove2.me/theorems/553487bd-4fb3-4949-88f2-3ab157a54d73
-- title:
--   Proposition 3.1 — one-step accelerated-gradient recursion (corrected: Bregman $V$, gradient of $f$)
-- statement:
--   Let $X$ be closed convex in a normed space, $\nu$ a distance generating function on $X$ with prox-function $V$, and $f$ differentiable along $X$ with $L$-Lipschitz gradient $\nabla f$ (3.3.2) satisfying the generalized strong convexity (3.3.3) $f(y)\ge f(x)+\langle\nabla f(x),y-x\rangle+\mu V(x,y)$ with $\mu\ge 0$. Given $x_{t-1},\bar x_{t-1}\in X$, let $\underline x_t=(1-q_t)\bar x_{t-1}+q_tx_{t-1}$ (3.3.4), $x_t=\arg\min_{x\in X}\{\gamma_t\langle\nabla f(\underline x_t),x\rangle+\mu V(\underline x_t,x)+V(x_{t-1},x)\}$ (3.3.5) and $\bar x_t=(1-\alpha_t)\bar x_{t-1}+\alpha_tx_t$ (3.3.6), with $0\le q_t<1$, $0<\alpha_t\le 1$, $\gamma_t>0$. If $q_t\le\alpha_t$ (3.3.7), $L(\alpha_t-q_t)/(1-q_t)\le\mu$ (3.3.8) and $Lq_t(1-\alpha_t)/(1-q_t)\le 1/\gamma_t$ (3.3.9), then for every $x\in X$
--   $$f(\bar x_t)-f(x)+\alpha_t\big(\mu+\tfrac1{\gamma_t}\big)V(x_t,x)\le(1-\alpha_t)\big[f(\bar x_{t-1})-f(x)\big]+\tfrac{\alpha_t}{\gamma_t}V(x_{t-1},x).$$
--
--   **Formalization Note.** The retired version took $V$ as a free function (with at most nonnegativity and a three-point identity), which admits $V\equiv 0$; the corrected version uses `FirstOrderOpt.Prox.DistanceGeneratingFunction.V`, the prox-function of a distance generating function on $X$ exactly as in §3.2. The gradient $\nabla f$ is tied to $f$ (`HasFDerivWithinAt` along $X$) with the Lipschitz condition (3.3.2) stated on $\nabla f$ itself, as in the book. The parameter ranges $q_t<1$ and $0<\alpha_t\le 1$ are the domain on which the ratios in (3.3.8)–(3.3.9) are genuine divisions (Lean's $x/0=0$ would otherwise make them vacuous). Closed convexity of $X$ is the standing assumption; membership of $\underline x_t$ and $\bar x_t$ in $X$ follows from convexity and is not assumed.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 65, Proposition 3.1, with (3.3.2)-(3.3.9)

import Mathlib
import Definitions.Def_FirstOrderOpt_Prox_DistanceGeneratingFunction

namespace FirstOrderOpt.Deterministic

open FirstOrderOpt.Prox

/-- Proposition 3.1 (the one-step accelerated-gradient recursion), Lan p. 65. Let `X` be closed
convex, `ν` a distance generating function on `X` with prox-function `V = ν.V`, and `f`
differentiable along `X` with gradient `fGrad`, `L`-smooth (3.3.2) and `μ`-generalized-strongly
convex with respect to `V` (3.3.3), `μ ≥ 0`. Given `(xPrev, xBarPrev) ∈ X × X`, form `xTilde` by
(3.3.4), `xNew` by the prox-mapping (3.3.5) and `xBarNew` by (3.3.6), with `0 ≤ q < 1`,
`0 < α ≤ 1`, `γ > 0`. If `q ≤ α` (3.3.7), `L(α - q)/(1 - q) ≤ μ` (3.3.8) and
`Lq(1 - α)/(1 - q) ≤ 1/γ` (3.3.9), then for every `x ∈ X`,
`f(xBarNew) - f(x) + α(μ + 1/γ)V(xNew, x) ≤ (1 - α)[f(xBarPrev) - f(x)] + (α/γ)V(xPrev, x)`.

Corrected version: `V` is the Bregman distance of a distance generating function (the retired
statement's free `V` with nonnegativity and a three-point identity admitted `V ≡ 0`), `fGrad` is
the gradient of `f` with `L`-Lipschitz gradient as in (3.3.2), `X` is closed convex, and the
parameter ranges `q < 1`, `0 < α ≤ 1` make the ratios in (3.3.8)–(3.3.9) genuine. -/
theorem accelerated_one_step_recursion_v2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (hXconv : Convex ℝ X) (hXclosed : IsClosed X)
    (ν : DistanceGeneratingFunction X)
    (f : E → ℝ) (L μ : ℝ) (hL : 0 < L) (hμ : 0 ≤ μ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hGrad : ∀ x ∈ X, HasFDerivWithinAt f (fGrad x) X x)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, ‖fGrad x - fGrad y‖ ≤ L * ‖x - y‖)
    (hStrConv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) + μ * ν.V x y ≤ f y)
    (xPrev xBarPrev xTilde xNew xBarNew : E)
    (hxPrev : xPrev ∈ X) (hxBarPrev : xBarPrev ∈ X) (hxNew : xNew ∈ X)
    (q γ α : ℝ) (hγ : 0 < γ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hTilde : xTilde = (1 - q) • xBarPrev + q • xPrev)
    (hNewMin : ∀ x ∈ X, γ * (fGrad xTilde) xNew + μ * ν.V xTilde xNew + ν.V xPrev xNew ≤
      γ * (fGrad xTilde) x + μ * ν.V xTilde x + ν.V xPrev x)
    (hBarNew : xBarNew = (1 - α) • xBarPrev + α • xNew)
    (h7 : q ≤ α) (h8 : L * (α - q) / (1 - q) ≤ μ) (h9 : L * q * (1 - α) / (1 - q) ≤ 1 / γ) :
    ∀ x ∈ X, f xBarNew - f x + α * (μ + 1 / γ) * ν.V xNew x ≤
      (1 - α) * (f xBarPrev - f x) + (α / γ) * ν.V xPrev x := by sorry

end FirstOrderOpt.Deterministic
