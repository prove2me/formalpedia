-- Prove2me | Theorems.Thm_ErrBoundQG_General_corollary_8_5
-- name    : ErrBoundQG.General.corollary_8_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:40.29851+00:00
-- url     : https://prove2.me/theorems/0cacae4c-dfb4-4fd0-879c-9e975264637a
-- title:
--   Corollary 8.5, p. 26 — a transverse constraint system F(x) ∈ Q is uniformly metrically regular under small affine perturbations
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ be $C^1$-smooth, let $Q\subset\mathbb R^m$ be closed, and consider the constraint system $F(x)\in Q$. Suppose $F$ is transverse to $Q$ at a point $\bar x$ with $F(\bar x)\in Q$, i.e. $\partial^\infty\delta_Q(F(\bar x))\cap\operatorname{Null}(\nabla F(\bar x)^*)=\{0\}$.
--
--   Then there are constants $\epsilon,\gamma>0$ and a neighbourhood $\mathcal X$ of $\bar x$ such that for every $x\in\mathcal X$ and every affine mapping $H(x)=Ax+b$ with $\|\nabla H\|<\epsilon$ and $\|H(\bar x)\|<\epsilon$ there is a point $z$ with
--   $$(F+H)(z)\in Q\qquad\text{and}\qquad\|x-z\|\le\gamma\cdot\operatorname{dist}\big((F+H)(x);Q\big).$$
--
--   This is the stability of constraint systems used, with $Q=\operatorname{epi}h$, in the proof of the comparison inequalities.
--
--   **Formalization Note** $\operatorname{dist}(\cdot;Q)$ is `Metric.infDist`, faithful here because $Q\ni F(\bar x)$ is nonempty. The constants and $\mathcal X$ are chosen before $x$ and $H$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 26, Corollary 8.5

import Mathlib
import Definitions.Def_ErrBoundQG_General_Setting

open scoped InnerProductSpace
open Filter Topology

namespace ErrBoundQG.General

theorem corollary_8_5 {n m : ℕ} (F : ErrBoundQG.ProxLin.En n → ErrBoundQG.ProxLin.En m) (hF : ContDiff ℝ 1 F)
    (Q : Set (ErrBoundQG.ProxLin.En m)) (hQ : IsClosed Q) (xbar : ErrBoundQG.ProxLin.En n)
    (htr : TransverseSet F Q xbar) (hFx : F xbar ∈ Q) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ X ∈ 𝓝 xbar,
      ∀ x ∈ X, ∀ (A : ErrBoundQG.ProxLin.En n →L[ℝ] ErrBoundQG.ProxLin.En m) (b : ErrBoundQG.ProxLin.En m), ‖A‖ < ε → ‖A xbar + b‖ < ε →
        ∃ z : ErrBoundQG.ProxLin.En n, F z + (A z + b) ∈ Q ∧
          ‖x - z‖ ≤ γ * Metric.infDist (F x + (A x + b)) Q := by sorry

end ErrBoundQG.General
