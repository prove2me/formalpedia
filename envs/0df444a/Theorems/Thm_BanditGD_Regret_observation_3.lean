-- Prove2me | Theorems.Thm_BanditGD_Regret_observation_3
-- name    : BanditGD.Regret.observation_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:05:14.381158+00:00
-- url     : https://prove2.me/theorems/96e24d05-a451-436e-8d18-ffc7aba3335a
-- title:
--   Observation 3, p. 8 — effective Lipschitz bound |c(x) − c(y)| ≤ (2C/αr)|x − y| for x ∈ (1−α)S
-- statement:
--   Let $S\subseteq\mathbb R^d$ be convex with $r\mathbb B\subseteq S$ for some $r>0$, let $0<\alpha\le1$, and let $f:\mathbb R^d\to\mathbb R$ be convex on $S$ with $|f(x)|\le C$ for all $x\in S$. Then for every $x\in(1-\alpha)S$ and every $y\in S$,
--   $$|f(x)-f(y)|\le\frac{2C}{\alpha r}\,|x-y| .$$
--
--   In the paper $f$ is any of the cost functions $c_t$. The bound acts as a Lipschitz constant $L=2C/(\alpha r)$ for bounded convex costs, which need not be Lipschitz on all of $S$.
--
--   **Formalization Note** The statement is for a single function $f$ standing for any $c_t$. Nothing is assumed about $f$ outside $S$.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 8, Observation 3

import Mathlib
open scoped Pointwise

namespace BanditGD.Regret

theorem observation_3 {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (C : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ S f) (hfC : ∀ x ∈ S, |f x| ≤ C) :
    ∀ x ∈ (1 - α) • S, ∀ y ∈ S, |f x - f y| ≤ 2 * C / (α * r) * ‖x - y‖ := by sorry

end BanditGD.Regret
