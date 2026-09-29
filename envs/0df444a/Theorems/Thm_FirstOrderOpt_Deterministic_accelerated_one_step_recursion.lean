-- Prove2me | Theorems.Thm_FirstOrderOpt_Deterministic_accelerated_one_step_recursion
-- name    : FirstOrderOpt.Deterministic.accelerated_one_step_recursion
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T20:58:35.150977+00:00
-- url     : https://prove2.me/theorems/4a7eb4c9-e3ce-4b92-ba0b-7a30840ae1be
-- title:
--   Proposition 3.1 — one-step accelerated-gradient recursion
-- statement:
--   Assume $f$ has $L$-Lipschitz gradient w.r.t. a general norm (Eq. (3.3.1)-(3.3.2)):
--   $f(y)-f(x)-\langle f'(x),y-x\rangle \le \tfrac{L}{2}\|y-x\|^2$, and is
--   $\mu$-generalized-strongly-convex w.r.t. the Bregman divergence $V$ (Eq. (3.3.3)):
--   $f(x)+\langle f'(x),y-x\rangle+\mu V(x,y) \le f(y)$, for all $x,y \in X$. Given
--   $(x_{t-1},\bar x_{t-1}) \in X\times X$, the accelerated gradient method forms
--   $$\tilde x_t = (1-q_t)\bar x_{t-1} + q_t x_{t-1} \quad \text{(3.3.4)},$$
--   $$x_t = \arg\min_{x\in X}\big\{\gamma_t[\langle f'(\tilde x_t),x\rangle + \mu V(\tilde
--   x_t,x)] + V(x_{t-1},x)\big\} \quad \text{(3.3.5)},$$
--   $$\bar x_t = (1-\alpha_t)\bar x_{t-1} + \alpha_t x_t \quad \text{(3.3.6)}.$$
--
--   **Proposition 3.1.** If $\alpha_t \ge q_t$ (3.3.7), $\dfrac{L(\alpha_t-q_t)}{1-q_t} \le \mu$
--   (3.3.8), and $\dfrac{Lq_t(1-\alpha_t)}{1-q_t} \le \dfrac1{\gamma_t}$ (3.3.9), then for every
--   $x \in X$,
--   $$f(\bar x_t)-f(x)+\alpha_t\Big(\mu+\tfrac1{\gamma_t}\Big)V(x_t,x) \le (1-\alpha_t)\big[f(\bar
--   x_{t-1})-f(x)\big] + \tfrac{\alpha_t}{\gamma_t}V(x_{t-1},x).$$
--
--   This single-step recursion is what both Theorem 3.6 (the nonstrongly-convex case, $\mu=0$)
--   and Theorem 3.7 (the strongly-convex case, $\mu>0$) specialize and telescope to get their
--   respective rates; it is the mission's central technical lemma.
--
--   **Formalization Note.** $f'$, the gradient/subgradient selector at each point, is a function
--   `fGrad : E → (E →L[ℝ] ℝ)`; $\tilde x_t$'s minimality property (3.3.5) is stated pointwise, as
--   in the mirror-descent milestones. This is a genuinely single-step statement (one instance of
--   $t$, with $x_{t-1},\bar x_{t-1}$ given data and $\tilde x_t, x_t, \bar x_t$ produced from
--   them) — the multi-step telescoping is `accelerated_gradient_recursion_bound` (Theorem 3.6)
--   below.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 65, Proposition 3.1

import Mathlib

namespace FirstOrderOpt.Deterministic

/-- Proposition 3.1 (the one-step accelerated-gradient recursion). `f` is `L`-smooth (3.3.2) and
`μ`-generalized-strongly-convex w.r.t. the Bregman divergence `V` (3.3.3), via a gradient
selector `fGrad`. Given `(xPrev, xBarPrev) ∈ X × X`, form `xTilde` by (3.3.4), `xNew` by the
prox-mapping (3.3.5), and `xBarNew` by (3.3.6). If `q ≤ α` (3.3.7), `L(α-q)/(1-q) ≤ μ` (3.3.8)
and `Lq(1-α)/(1-q) ≤ 1/γ` (3.3.9), then for every `x ∈ X`,
`f(xBarNew) - f(x) + α(μ+1/γ)V(xNew,x) ≤ (1-α)[f(xBarPrev)-f(x)] + (α/γ)V(xPrev,x)`. `V` is
pinned down to a genuine Bregman divergence (nonnegative, three-point identity (3.2.6) via `dV`,
matching Lemma 3.5, p. 65): the proof needs the identity applied at both centers `xTilde` and
`xPrev` of the combined `μ·V(xTilde,·) + V(xPrev,·)` prox-mapping `hNewMin`, plus the
strong-convexity lower bound on `V` in bounding `‖dt‖²`. -/
theorem accelerated_one_step_recursion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Set E) (f : E → ℝ) (V : E → E → ℝ) (dV : E → E → E →L[ℝ] ℝ) (L μ : ℝ) (hL : 0 < L)
    (hμ : 0 ≤ μ)
    (fGrad : E → E →L[ℝ] ℝ)
    (hSmooth : ∀ x ∈ X, ∀ y ∈ X, f y - f x - (fGrad x) (y - x) ≤ (L / 2) * ‖y - x‖ ^ 2)
    (hStrConv : ∀ x ∈ X, ∀ y ∈ X, f x + (fGrad x) (y - x) + μ * V x y ≤ f y)
    (hVnonneg : ∀ x ∈ X, ∀ z ∈ X, 0 ≤ V x z)
    (hVthreepoint : ∀ x ∈ X, ∀ y ∈ X, ∀ z ∈ X, V x z = V x y + (dV x y) (z - y) + V y z)
    (xPrev xBarPrev xTilde xNew xBarNew : E)
    (hxPrev : xPrev ∈ X) (hxBarPrev : xBarPrev ∈ X) (hxTilde : xTilde ∈ X) (hxNew : xNew ∈ X)
    (hxBarNew : xBarNew ∈ X)
    (q γ α : ℝ) (hγ : 0 < γ)
    (hTilde : xTilde = (1 - q) • xBarPrev + q • xPrev)
    (hNewMin : ∀ x ∈ X, γ * (fGrad xTilde) xNew + μ * V xTilde xNew + V xPrev xNew ≤
      γ * (fGrad xTilde) x + μ * V xTilde x + V xPrev x)
    (hBarNew : xBarNew = (1 - α) • xBarPrev + α • xNew)
    (h7 : q ≤ α) (h8 : L * (α - q) / (1 - q) ≤ μ) (h9 : L * q * (1 - α) / (1 - q) ≤ 1 / γ) :
    ∀ x ∈ X, f xBarNew - f x + α * (μ + 1 / γ) * V xNew x ≤
      (1 - α) * (f xBarPrev - f x) + (α / γ) * V xPrev x := by sorry

end FirstOrderOpt.Deterministic
