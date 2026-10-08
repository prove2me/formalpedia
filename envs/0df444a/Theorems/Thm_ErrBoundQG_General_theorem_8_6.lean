-- Prove2me | Theorems.Thm_ErrBoundQG_General_theorem_8_6
-- name    : ErrBoundQG.General.theorem_8_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:30.290901+00:00
-- url     : https://prove2.me/theorems/07f3e95d-e3e2-4b9b-a131-694281f9779d
-- title:
--   Theorem 8.6, p. 27 — comparison inequalities between φ(y) and the linearization φ(x; ·) after a small move of y
-- statement:
--   Consider the composite problem $\min_x\varphi(x)=h(c(x))$ with $c:\mathbb R^n\to\mathbb R^m$ $C^1$-smooth and $h:\mathbb R^m\to\overline{\mathbb R}$ closed, and its linearization $\varphi(x;y)=h(c(x)+\nabla c(x)(y-x))$. Let $\bar x\in\operatorname{dom}\varphi$ with $c\pitchfork_{\bar x}h$, and suppose $\nabla c$ is Lipschitz continuous around $\bar x$.
--
--   Then there exist $\epsilon,\gamma>0$ and a neighbourhood $\mathcal X$ of $\bar x$ such that:
--
--   1. for any $x,y\in\mathcal X$ with $|\varphi(y)-\varphi(\bar x)|<\epsilon$ there is a point $y^-$ with
--   $$\|y-y^-\|\le\gamma\|y-x\|^2\quad\text{and}\quad\varphi(x;y^-)\le\varphi(y)+\gamma\|y-x\|^2;$$
--   2. for any $x,y\in\mathcal X$ with $|\varphi(x;y)-\varphi(\bar x)|<\epsilon$ there is a point $y^+$ with
--   $$\|y-y^+\|\le\gamma\|y-x\|^2\quad\text{and}\quad\varphi(y^+)\le\varphi(x;y)+\gamma\|y-x\|^2.$$
--
--   When $h$ is extended-valued, $\varphi(y)$ and $\varphi(x;y)$ cannot be compared directly (one may be finite and the other infinite); the theorem compares them after a quadratically small move of the point, and plays the role of the inequalities (5.2) of the finite-valued setting.
--
--   **Formalization Note** $h$ is `EReal`-valued, lower semicontinuous and never $-\infty$. $|a-\varphi(\bar x)|<\epsilon$ requires $a$ finite. "$\nabla c$ is Lipschitz around $\bar x$" is a bound $\|\nabla c(x)-\nabla c(y)\|\le\beta\|x-y\|$ in operator norm on a neighbourhood of $\bar x$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 27, Theorem 8.6

import Mathlib
import Definitions.Def_ErrBoundQG_General_Setting

open scoped InnerProductSpace
open Filter Topology

namespace ErrBoundQG.General

theorem theorem_8_6 {n m : ℕ} (c : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (hc : ContDiff ℝ 1 c)
    (h : ErrBoundQG.ProxLin.En m → EReal) (hlsc : LowerSemicontinuous h) (hbot : ∀ y, h y ≠ ⊥)
    (xbar : ErrBoundQG.ProxLin.En n) (hdom : phi h c xbar ≠ ⊤) (htr : Transverse c h xbar)
    (hlip : JacLipAround c xbar) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ X ∈ 𝓝 xbar,
      (∀ x ∈ X, ∀ y ∈ X, ENear (phi h c y) (phi h c xbar) ε →
        ∃ ym : ErrBoundQG.ProxLin.En n, ‖y - ym‖ ≤ γ * ‖y - x‖ ^ 2 ∧
          phiLin h c x ym ≤ phi h c y + ((γ * ‖y - x‖ ^ 2 : ℝ) : EReal)) ∧
      (∀ x ∈ X, ∀ y ∈ X, ENear (phiLin h c x y) (phi h c xbar) ε →
        ∃ yp : ErrBoundQG.ProxLin.En n, ‖y - yp‖ ≤ γ * ‖y - x‖ ^ 2 ∧
          phi h c yp ≤ phiLin h c x y + ((γ * ‖y - x‖ ^ 2 : ℝ) : EReal)) := by sorry

end ErrBoundQG.General
