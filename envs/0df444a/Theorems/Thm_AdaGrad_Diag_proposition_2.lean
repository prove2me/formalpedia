-- Prove2me | Theorems.Thm_AdaGrad_Diag_proposition_2
-- name    : AdaGrad.Diag.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:14.637354+00:00
-- url     : https://prove2.me/theorems/9d48ff0a-350c-46a1-afa5-1e6e8c97b2d4
-- title:
--   Proposition 2 — regret of primal-dual subgradient (dual averaging) with time-varying proximal functions, (10)
-- statement:
--   Let $\eta>0$, let $\mathcal X\subseteq\mathbb R^d$ be closed and convex with $0\in\mathcal X$, and let $\varphi$ and every $f_t$ be convex functions $\mathbb R^d\to\mathbb R$, with $\varphi$ minimized over $\mathcal X$ at $0$. For $t=0,1,2,\dots$ let $h_t\in\mathbb R^d$ have positive entries, non-decreasing in $t$ ($h_{t,i}\le h_{t+1,i}$), and let $\psi_t(y)=\frac12\sum_ih_{t,i}y_i^2$, so that $\psi_{t+1}\ge\psi_t$, with squared dual norm $\|g\|^2_{\psi_t^*}=\sum_ig_i^2/h_{t,i}$. Let $x_1=0$ and let $x_1,x_2,\dots$ be a run of the primal-dual subgradient update (3): $g_t$ is a subgradient of $f_t$ at $x_t$ and $x_{t+1}\in\mathcal X$ minimizes
--   $$\eta\Big\langle\frac1t\sum_{\tau=1}^tg_\tau,y\Big\rangle+\eta\varphi(y)+\frac1t\psi_t(y)$$
--   over $\mathcal X$, for every $t\ge1$. Then for every $T$ and every $x^*\in\mathcal X$,
--   $$\sum_{t=1}^T\big[f_t(x_t)+\varphi(x_t)-f_t(x^*)-\varphi(x^*)\big]\le\frac1\eta\psi_T(x^*)+\frac\eta2\sum_{t=1}^T\|g_t\|^2_{\psi_{t-1}^*}.$$
--
--   This is the regret bound of dual averaging when the proximal function may grow from round to round; note that round $t$'s subgradient is measured in the dual norm of the previous round's proximal function.
--
--   **Formalization Note** Specialised to diagonal quadratic proximal functions; the standing assumptions of §2 (p. 2129), $\psi_{t+1}\ge\psi_t$ and 1-strong convexity of $\psi_t$ with respect to $\|\cdot\|_{\psi_t}$, are the monotonicity of the weights and the quadratic form. The weights are taken strictly positive, so every dual norm is finite. The proof's "recalling that $x_1=\operatorname{argmin}_{x\in\mathcal X}\varphi(x)$" (p. 2153) and the identity $\nabla\psi_0^*(0)=x_1$ it uses are made explicit, with Figure 1's initialization, as $x_1=0\in\mathcal X$ and $\varphi(0)\le\varphi(y)$ for $y\in\mathcal X$.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2129, Proposition 2, (10), standing assumptions of §2; proof pp. 2152–2153

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), Proposition 2, (10), p. 2129, specialised to diagonal
quadratic proximal functions `ψ_t(y) = ½ ∑_i h_{t,i} y_i²` (`t = 0, 1, 2, …`) with positive weights
that are non-decreasing in `t` (so `ψ_{t+1} ≥ ψ_t`, the standing assumption of §2). Let the `f_t`
and `ϕ` be convex, `X` closed and convex with `0 ∈ X`, let `x_1 = 0` minimize `ϕ` over `X`, and let
`x_1, x_2, …` be a run of the primal-dual subgradient update (3) with subgradients `g_t` of `f_t` at
`x_t`. Then for every `T` and every `x* ∈ X`,
`∑_{t=1}^T [f_t(x_t) + ϕ(x_t) − f_t(x*) − ϕ(x*)] ≤ (1/η) ψ_T(x*) + (η/2) ∑_{t=1}^T ‖g_t‖²_{ψ_{t−1}*}`,
with `‖g‖²_{ψ*} = ∑_i g_i² / h_i`. -/
theorem proposition_2 {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (hXcl : IsClosed X) (hX0 : (0 : EuclideanSpace ℝ (Fin d)) ∈ X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (hϕ0 : ∀ y ∈ X, ϕ 0 ≤ ϕ y)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (h : ℕ → Fin d → ℝ) (hpos : ∀ t i, 0 < h t i) (hmono : ∀ t i, h t i ≤ h (t + 1) i)
    (x g : ℕ → EuclideanSpace ℝ (Fin d)) (hx1 : x 1 = 0)
    (hrun : IsDualAveragingRun η X ϕ f h x g)
    (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    regret f ϕ x xstar T
      ≤ 1 / η * prox (h T) xstar
        + η / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (h (t - 1)) (g t) := by sorry

end AdaGrad.Diag
