-- Prove2me | Theorems.Thm_AdaGrad_Diag_proposition_3
-- name    : AdaGrad.Diag.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:31:05.823621+00:00
-- url     : https://prove2.me/theorems/c188208d-cf07-48fd-916f-03a50eaa0796
-- title:
--   Proposition 3 — regret of composite mirror descent with time-varying proximal functions, (11)
-- statement:
--   Let $\eta>0$, let $\mathcal X\subseteq\mathbb R^d$ be closed and convex, and let $\varphi$ and every $f_t$ be convex functions $\mathbb R^d\to\mathbb R$. For each round $t\ge1$ let $h_t\in\mathbb R^d$ have nonnegative entries, with proximal function $\psi_t(y)=\frac12\sum_ih_{t,i}y_i^2$, Bregman divergence $B_{\psi_t}(y,z)=\frac12\sum_ih_{t,i}(y_i-z_i)^2$ and squared dual norm $\|g\|^2_{\psi_t^*}=\sum_ig_i^2/h_{t,i}$. Let $x_1,x_2,\dots$ be a run of the composite mirror descent update (4): $g_t$ is a subgradient of $f_t$ at $x_t$, with $g_{t,i}=0$ whenever $h_{t,i}=0$, and $x_{t+1}\in\mathcal X$ minimizes $\eta\langle g_t,y\rangle+\eta\varphi(y)+B_{\psi_t}(y,x_t)$ over $\mathcal X$. Assume $x_1\in\mathcal X$ minimizes $\varphi$ over $\mathcal X$. Then for every $T$ and every $x^*\in\mathcal X$,
--   $$\sum_{t=1}^T\big[f_t(x_t)+\varphi(x_t)-f_t(x^*)-\varphi(x^*)\big]\le\frac1\eta B_{\psi_1}(x^*,x_1)+\frac1\eta\sum_{t=1}^{T-1}\big[B_{\psi_{t+1}}(x^*,x_{t+1})-B_{\psi_t}(x^*,x_{t+1})\big]+\frac\eta2\sum_{t=1}^T\|g_t\|^2_{\psi_t^*}.$$
--
--   This reduces the regret of composite mirror descent with adaptive proximal functions to two terms: the drift of the Bregman divergences and the dual norms of the subgradients.
--
--   **Formalization Note** Specialised to diagonal quadratic proximal functions; their strong convexity with respect to $\|\cdot\|_{\psi_t}$ is implied by the quadratic form, and no monotonicity of $h_t$ is needed. The paper's "assume w.l.o.g. that $\varphi(x_1)=0$" is used in its proof as $\varphi(x_1)\le\varphi(x_{T+1})$; here it is the hypothesis that $x_1$ minimizes $\varphi$ over $\mathcal X$ (without it the inequality fails). The condition "$h_{t,i}=0\Rightarrow g_{t,i}=0$" makes Lean's $a/0=0$ agree with the paper's dual norm.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2129, Proposition 3, (11); proof p. 2154

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

/-- Duchi, Hazan, Singer, JMLR 12 (2011), Proposition 3, (11), p. 2129, specialised to diagonal
quadratic proximal functions `ψ_t(y) = ½ ∑_i h_{t,i} y_i²` with weights `h_{t,i} ≥ 0`. Let the
`f_t` and `ϕ` be convex, `X` convex, and let `x_1, x_2, …` be a run of the composite mirror descent
update (4) with subgradients `g_t` of `f_t` at `x_t`, where `h_{t,i} = 0` forces `g_{t,i} = 0`.
Assume `x_1 ∈ X` minimizes `ϕ` over `X` (the paper's "w.l.o.g. `ϕ(x_1) = 0`", see the
Formalization Note). Then for every `T` and every `x* ∈ X`,
`∑_{t=1}^T [f_t(x_t) + ϕ(x_t) − f_t(x*) − ϕ(x*)]
   ≤ (1/η) B_{ψ_1}(x*, x_1) + (1/η) ∑_{t=1}^{T−1} [B_{ψ_{t+1}}(x*, x_{t+1}) − B_{ψ_t}(x*, x_{t+1})]
     + (η/2) ∑_{t=1}^T ‖g_t‖²_{ψ_t*}`. -/
theorem proposition_3 {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (hXcl : IsClosed X)
    (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (f : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ t, ConvexOn ℝ Set.univ (f t))
    (h : ℕ → Fin d → ℝ) (x g : ℕ → EuclideanSpace ℝ (Fin d))
    (hh : ∀ t, 1 ≤ t → ∀ i, 0 ≤ h t i)
    (hhg : ∀ t, 1 ≤ t → ∀ i, h t i = 0 → g t i = 0)
    (hrun : IsCompositeMDRun η X ϕ f h x g)
    (hx1 : x 1 ∈ X) (hϕx1 : ∀ y ∈ X, ϕ (x 1) ≤ ϕ y)
    (T : ℕ) (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    regret f ϕ x xstar T
      ≤ 1 / η * bregman (h 1) xstar (x 1)
        + 1 / η * ∑ t ∈ Finset.Ico 1 T,
            (bregman (h (t + 1)) xstar (x (t + 1)) - bregman (h t) xstar (x (t + 1)))
        + η / 2 * ∑ t ∈ Finset.Icc 1 T, dualNormSq (h t) (g t) := by sorry

end AdaGrad.Diag
