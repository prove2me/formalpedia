-- Prove2me | Theorems.Thm_ErrBoundQG_General_theorem_8_9
-- name    : ErrBoundQG.General.theorem_8_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:28.22151+00:00
-- url     : https://prove2.me/theorems/9fc2d6aa-450e-4cf8-8502-8d79472a4deb
-- title:
--   Theorem 8.9, p. 29 — a stationary point xᵗ of the proximal subproblem is close to a nearly stationary point x̂ of φ
-- statement:
--   Consider the composite problem (8.2), $\varphi=h\circ c$, with $c:\mathbb R^n\to\mathbb R^m$ $C^1$-smooth and $h$ closed, and a point $\bar x$ with $c\pitchfork_{\bar x}h$ and $0\in\partial\varphi(\bar x)$. Suppose $\nabla c$ is locally Lipschitz around $\bar x$ and $h$ is prox-regular at $c(\bar x)$ for every subgradient $w\in\partial h(c(\bar x))$ with $0=\nabla c(\bar x)^*w$.
--
--   Then there are constants $\gamma,\epsilon,a,b>0$ and a neighbourhood $\mathcal X$ of $\bar x$ such that for any $t>0$, $x\in\mathcal X$ and $x^t\in\mathcal X\cap\mathcal S_t(x)$ with $|\varphi(x;x^t)-\varphi(\bar x)|<\epsilon$ there is a point $\hat x$ with
--
--   1. (point proximity) $\|x^t-\hat x\|\le(1+\gamma\|x^t-x\|)\cdot\|x^t-x\|$;
--   2. (functional proximity) $\varphi(\hat x)\le\varphi(x;x^t)+(a+b/t)\cdot\|x^t-x\|^2$;
--   3. (near-stationarity)
--   $$\operatorname{dist}(0;\partial\varphi(\hat x))\le(a+b/t)\cdot\|x^t-x\| .$$
--
--   This generalizes Theorem 5.3 to extended-valued, nonconvex $h$ and is the main tool for Theorem 8.11.
--
--   **Formalization Note** The constants and $\mathcal X$ are chosen before $t$. $\mathcal S_t(x)$ is the set of limiting-stationary points of $\varphi_t(x;\cdot)$. (iii) is stated as the existence of $v\in\partial\varphi(\hat x)$ with $\|v\|\le(a+b/t)\|x^t-x\|$; this is equivalent to the distance bound because the limiting subdifferential is closed, and it is false, as on the page, when $\partial\varphi(\hat x)=\varnothing$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 29, Theorem 8.9

import Mathlib
import Definitions.Def_ErrBoundQG_General_Setting

open scoped InnerProductSpace
open Filter Topology

namespace ErrBoundQG.General

theorem theorem_8_9 {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (hc : ContDiff ℝ 1 c)
    (h : ErrBoundQG.ProxLin.En m → EReal) (hlsc : LowerSemicontinuous h) (hbot : ∀ y, h y ≠ ⊥)
    (xbar : ErrBoundQG.ProxLin.En n) (htr : Transverse c h xbar) (hstat : 0 ∈ limSubdiff (phi h c) xbar)
    (hlip : JacLipAround c xbar)
    (hpr : ∀ w ∈ limSubdiff h (c xbar),
      ContinuousLinearMap.adjoint (fderiv ℝ c xbar) w = 0 → ProxRegularAt h (c xbar) w) :
    ∃ γ ε a b : ℝ, 0 < γ ∧ 0 < ε ∧ 0 < a ∧ 0 < b ∧ ∃ X ∈ 𝓝 xbar,
      ∀ t : ℝ, 0 < t → ∀ x ∈ X, ∀ xt ∈ X ∩ statMap h c t x,
        ENear (phiLin h c x xt) (phi h c xbar) ε →
          ∃ xhat : ErrBoundQG.ProxLin.En n,
            ‖xt - xhat‖ ≤ (1 + γ * ‖xt - x‖) * ‖xt - x‖ ∧
            phi h c xhat ≤ phiLin h c x xt + (((a + b / t) * ‖xt - x‖ ^ 2 : ℝ) : EReal) ∧
            ∃ v ∈ limSubdiff (phi h c) xhat, ‖v‖ ≤ (a + b / t) * ‖xt - x‖ := by sorry

end ErrBoundQG.General
