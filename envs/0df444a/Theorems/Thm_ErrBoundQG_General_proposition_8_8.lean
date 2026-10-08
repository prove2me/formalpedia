-- Prove2me | Theorems.Thm_ErrBoundQG_General_proposition_8_8
-- name    : ErrBoundQG.General.proposition_8_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:07.550986+00:00
-- url     : https://prove2.me/theorems/2b827064-aa44-4ee8-8395-57ac3d98bb12
-- title:
--   Proposition 8.8, p. 28 — the linearized subproblems φ(x; ·) inherit transversality and are prox-regular at x̄, uniformly in x
-- statement:
--   Consider the composite problem (8.2), $\varphi=h\circ c$, with $c$ $C^1$-smooth and $h$ closed, and let $\bar x\in\operatorname{dom}\varphi$ with $c\pitchfork_{\bar x}h$. Then:
--
--   1. There exist a neighbourhood $\mathcal X$ of $\bar x$ and $\epsilon>0$ such that the affine maps $z\mapsto c(x)+\nabla c(x)(z-x)$ are transverse to $h$ at $z$ for all $x,z\in\mathcal X$ with $|\varphi(x;z)-\varphi(\bar x)|<\epsilon$.
--   2. Let $\bar v\in\partial\varphi(\bar x)$, suppose $\nabla c$ is Lipschitz continuous around $\bar x$ and $h$ is prox-regular at $c(\bar x)$ for every $w\in\partial h(c(\bar x))$ with $\bar v=\nabla c(\bar x)^*w$. Then, after possibly shrinking $\mathcal X$ and $\epsilon$, there are a neighbourhood $\mathcal V$ of $\bar v$ and $\gamma>0$ such that
--   $$\varphi(x;y)\ge\varphi(x;z)+\langle v,y-z\rangle-\frac\gamma2\|y-z\|^2\qquad(8.4)$$
--   for all $x,y,z\in\mathcal X$ with $|\varphi(x;z)-\varphi(\bar x)|<\epsilon$ and every $v\in\mathcal V\cap\partial_z\varphi(x;z)$, the limiting subdifferential of $\varphi(x;\cdot)$ at $z$.
--
--   So the linearized functions are prox-regular at $\bar x$ for $\bar v$ uniformly in $x$; this is the quadratic minorant used in Theorems 8.9 and 8.11.
--
--   **Formalization Note** "After possibly shrinking" is stated as new $\mathcal X'\subseteq\mathcal X$, $0<\epsilon'\le\epsilon$ chosen after $\bar v$; part 1 stays valid on the smaller sets. $|\cdot|<\epsilon$ requires finite values; $h$ is `EReal`-valued, lower semicontinuous, never $-\infty$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 28, Proposition 8.8 (8.4)

import Mathlib
import Definitions.Def_ErrBoundQG_General_Setting

open scoped InnerProductSpace
open Filter Topology

namespace ErrBoundQG.General

theorem proposition_8_8 {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (hc : ContDiff ℝ 1 c)
    (h : ErrBoundQG.ProxLin.En m → EReal) (hlsc : LowerSemicontinuous h) (hbot : ∀ y, h y ≠ ⊥)
    (xbar : ErrBoundQG.ProxLin.En n) (hdom : phi h c xbar ≠ ⊤) (htr : Transverse c h xbar) :
    ∃ X ∈ 𝓝 xbar, ∃ ε : ℝ, 0 < ε ∧
      (∀ x ∈ X, ∀ z ∈ X, ENear (phiLin h c x z) (phi h c xbar) ε →
        Transverse (fun w => c x + fderiv ℝ c x (w - x)) h z) ∧
      (∀ vbar ∈ limSubdiff (phi h c) xbar, JacLipAround c xbar →
        (∀ w ∈ limSubdiff h (c xbar),
          vbar = ContinuousLinearMap.adjoint (fderiv ℝ c xbar) w → ProxRegularAt h (c xbar) w) →
        ∃ X' ∈ 𝓝 xbar, X' ⊆ X ∧ ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧
          ∃ V ∈ 𝓝 vbar, ∃ γ : ℝ, 0 < γ ∧
            ∀ x ∈ X', ∀ y ∈ X', ∀ z ∈ X', ENear (phiLin h c x z) (phi h c xbar) ε' →
              ∀ v ∈ V ∩ limSubdiff (phiLin h c x) z,
                phiLin h c x z + ((⟪v, y - z⟫_ℝ - γ / 2 * ‖y - z‖ ^ 2 : ℝ) : EReal) ≤
                  phiLin h c x y) := by sorry

end ErrBoundQG.General
