-- Prove2me | Theorems.Thm_ErrBoundQG_General_theorem_8_4
-- name    : ErrBoundQG.General.theorem_8_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:24:09.092211+00:00
-- url     : https://prove2.me/theorems/cbc95aa2-4bb6-454a-ac55-7f0a26095d0a
-- title:
--   Theorem 8.4, p. 26 — metric regularity of a closed set-valued map survives small affine perturbations, uniformly
-- statement:
--   Let $G:\mathbb R^n\rightrightarrows\mathbb R^m$ be a set-valued mapping with closed graph that is metrically regular around a point $(\bar x,\bar y)\in\operatorname{gph}G$ (with some constant). For an affine mapping $H(x)=Ax+b$ write $(G+H)(x)=G(x)+H(x)$ and $(G+H)^{-1}(y)=\{z: y\in(G+H)(z)\}$.
--
--   Then there exist constants $\epsilon,\gamma>0$ and neighbourhoods $\mathcal X$ of $\bar x$ and $\mathcal Y$ of $\bar y$ such that
--   $$\operatorname{dist}\big(x,(G+H)^{-1}(y)\big)\le\gamma\cdot\operatorname{dist}\big(y,(G+H)(x)\big)$$
--   for every affine $H$ with $\|\nabla H\|=\|A\|<\epsilon$, every $x\in\mathcal X$ and every $y\in H(\bar x)+\mathcal Y$.
--
--   Metric regularity, unlike subregularity, is stable under small linear perturbations; this uniform version is the tool behind the comparison inequalities of Theorem 8.6.
--
--   **Formalization Note** Distances to an empty set are $+\infty$: the inequality is stated for every $v\in(G+H)(x)$ with $\|y-v\|$ on the right, and then $(G+H)^{-1}(y)$ is required to be nonempty. $y\in H(\bar x)+\mathcal Y$ is written $y=(A\bar x+b)+u$ with $u\in\mathcal Y$. The constants and neighbourhoods are chosen before $H$.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 26, Theorem 8.4

import Mathlib
import Definitions.Def_ErrBoundQG_General_Setting

open scoped InnerProductSpace
open Filter Topology

namespace ErrBoundQG.General

theorem theorem_8_4 {n m : ℕ} (G : ErrBoundQG.ProxLin.En n → Set (ErrBoundQG.ProxLin.En m))
    (hG : IsClosed {p : ErrBoundQG.ProxLin.En n × ErrBoundQG.ProxLin.En m | p.2 ∈ G p.1})
    (xbar : ErrBoundQG.ProxLin.En n) (ybar : ErrBoundQG.ProxLin.En m) (hreg : ∃ l : ℝ, IsMetricRegularAround G xbar ybar l) :
    ∃ ε γ : ℝ, 0 < ε ∧ 0 < γ ∧ ∃ X ∈ 𝓝 xbar, ∃ Y ∈ 𝓝 ybar,
      ∀ (A : ErrBoundQG.ProxLin.En n →L[ℝ] ErrBoundQG.ProxLin.En m) (b : ErrBoundQG.ProxLin.En m), ‖A‖ < ε →
        ∀ x ∈ X, ∀ u ∈ Y, ∀ v ∈ affPert G A b x,
          (setInv (affPert G A b) ((A xbar + b) + u)).Nonempty ∧
            Metric.infDist x (setInv (affPert G A b) ((A xbar + b) + u)) ≤
              γ * ‖((A xbar + b) + u) - v‖ := by sorry

end ErrBoundQG.General
