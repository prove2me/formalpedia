-- Prove2me | Theorems.Thm_BanditGD_Regret_points_mem
-- name    : BanditGD.Regret.points_mem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:28:21.306388+00:00
-- url     : https://prove2.me/theorems/86cf73f2-daf8-44ac-855a-fe783e2d5720
-- title:
--   Proof of Theorem 1, p. 8 — the iterates lie in (1−α)S and the played points xₜ lie in S when δ ≤ αr, α ≤ 1
-- statement:
--   Let $S\subseteq\mathbb R^d$ be convex with $r\mathbb B\subseteq S$ for some $r>0$, and let $\delta>0$, $\alpha\le1$ with
--   $$\delta\le\alpha r .$$
--   Let $u_1,u_2,\dots$ be unit vectors, $c_1,c_2,\dots:\mathbb R^d\to\mathbb R$ arbitrary, $\nu\in\mathbb R$, and let $y_1,y_2,\dots$ be a run of $\mathrm{BGD}(\alpha,\delta,\nu)$ on $S$ with these directions. Then for every $t\ge1$,
--   $$y_t\in(1-\alpha)S\qquad\text{and}\qquad x_t=y_t+\delta u_t\in S .$$
--
--   So the bandit algorithm only ever plays feasible points. The paper's condition is $\delta/r\le\alpha<1$, which Theorem 1's parameters satisfy for $n\ge(3Rd/2r)^2$.
--
--   **Formalization Note** The statement is deterministic (one realization of the directions). The paper's $\alpha<1$ is relaxed to $\alpha\le1$: at the threshold $n=(3Rd/2r)^2$ Theorem 1's $\alpha$ equals $1$, and the claim still holds there ($(1-\alpha)S=\{0\}$).
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 8, proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_OSGD
import Definitions.Def_BanditGD_Regret_Setting
open scoped Pointwise

namespace BanditGD.Regret

theorem points_mem {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S)
    (α δ ν : ℝ) (hδ : 0 < δ) (hδα : δ ≤ α * r) (hα1 : α ≤ 1)
    (c : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (u y : ℕ → EuclideanSpace ℝ (Fin d)) (hu : ∀ t, ‖u t‖ = 1)
    (hrun : IsBGDRun S α δ ν c u y) :
    ∀ t, 1 ≤ t → y t ∈ (1 - α) • S ∧ y t + δ • u t ∈ S := by sorry

end BanditGD.Regret
