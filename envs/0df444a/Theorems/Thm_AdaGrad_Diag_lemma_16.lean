-- Prove2me | Theorems.Thm_AdaGrad_Diag_lemma_16
-- name    : AdaGrad.Diag.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:30:49.500153+00:00
-- url     : https://prove2.me/theorems/a8ff6a3b-2b03-4ea9-828a-d365befd1f48
-- title:
--   Lemma 16 — one step of composite mirror descent (diagonal quadratic proximal functions)
-- statement:
--   Let $\eta>0$, let $\mathcal X\subseteq\mathbb R^d$ be convex, and let $\varphi$ and $f_t$ be convex functions $\mathbb R^d\to\mathbb R$. Let $h\in\mathbb R^d$ have nonnegative entries and write $\psi_t(y)=\frac12\sum_i h_iy_i^2$, so that $B_{\psi_t}(y,z)=\frac12\sum_ih_i(y_i-z_i)^2$ and $\|g\|^2_{\psi_t^*}=\sum_i g_i^2/h_i$. Let $g_t$ be a subgradient of $f_t$ at $x_t$ with $g_{t,i}=0$ whenever $h_i=0$, and let $x_{t+1}\in\mathcal X$ minimize $\eta\langle g_t,y\rangle+\eta\varphi(y)+B_{\psi_t}(y,x_t)$ over $y\in\mathcal X$ (one step of the composite mirror descent update (4)). Then for every $x^*\in\mathcal X$,
--   $$\eta\big(f_t(x_t)-f_t(x^*)\big)+\eta\big(\varphi(x_{t+1})-\varphi(x^*)\big)\le B_{\psi_t}(x^*,x_t)-B_{\psi_t}(x^*,x_{t+1})+\frac{\eta^2}{2}\|g_t\|^2_{\psi_t^*}.$$
--
--   This is the one-step inequality that, summed over rounds, gives the regret bound of composite mirror descent with time-varying proximal functions (Proposition 3).
--
--   **Formalization Note** Specialised to diagonal quadratic proximal functions $\psi_t(y)=\frac12\sum_ih_{t,i}y_i^2$; the paper's strong convexity of $B_{\psi_t}$ with respect to $\|\cdot\|_{\psi_t}$ is implied by the quadratic form. The comparator is required to lie in $\mathcal X$: the page says "for any $x^*$", but its proof applies the optimality condition of $x_{t+1}$, valid for points of $\mathcal X$, at $x=x^*$. The condition "$h_i=0\Rightarrow g_{t,i}=0$" makes Lean's $a/0=0$ agree with the paper's dual norm, which is $+\infty$ otherwise.
-- source:
--   Duchi, Hazan, Singer, Adaptive Subgradient Methods for Online Learning and Stochastic Optimization, JMLR 12 (2011), p. 2154, Lemma 16

import Mathlib
import Definitions.Def_AdaGrad_Diag_Setup

namespace AdaGrad.Diag

open ShorNonsmooth.AlmostDiff

/-- Duchi, Hazan, Singer, JMLR 12 (2011), Lemma 16, p. 2154, specialised to diagonal quadratic
proximal functions `ψ_t(y) = ½ ∑_i h_i y_i²` with weights `h_i ≥ 0`: one step of the composite
mirror descent update (4). Let `g_t` be a subgradient of the convex `f_t` at `x_t`, and let
`x_{t+1} ∈ X` minimize `η⟨g_t, y⟩ + ηϕ(y) + B_{ψ_t}(y, x_t)` over the convex set `X`, where `ϕ` is
convex. If `h_i = 0` forces `g_{t,i} = 0`, then for every `x* ∈ X`,
`η(f_t(x_t) − f_t(x*)) + η(ϕ(x_{t+1}) − ϕ(x*))
   ≤ B_{ψ_t}(x*, x_t) − B_{ψ_t}(x*, x_{t+1}) + (η²/2) ‖g_t‖²_{ψ_t*}`,
with `‖g‖²_{ψ_t*} = ∑_i g_i² / h_i`. -/
theorem lemma_16 {d : ℕ} (η : ℝ) (hη : 0 < η) (X : Set (EuclideanSpace ℝ (Fin d)))
    (hXc : Convex ℝ X) (ϕ : EuclideanSpace ℝ (Fin d) → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (ft : EuclideanSpace ℝ (Fin d) → ℝ) (hft : ConvexOn ℝ Set.univ ft)
    (h : Fin d → ℝ) (hh : ∀ i, 0 ≤ h i)
    (xt xnext gt : EuclideanSpace ℝ (Fin d))
    (hhg : ∀ i, h i = 0 → gt i = 0)
    (hsub : IsSubgradient ft xt gt) (hmem : xnext ∈ X)
    (hmin : IsMinOn (fun y => η * inner ℝ gt y + η * ϕ y + bregman h y xt) X xnext)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : xstar ∈ X) :
    η * (ft xt - ft xstar) + η * (ϕ xnext - ϕ xstar)
      ≤ bregman h xstar xt - bregman h xstar xnext + η ^ 2 / 2 * dualNormSq h gt := by sorry

end AdaGrad.Diag
