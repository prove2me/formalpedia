-- Prove2me | Theorems.Thm_BanditGD_Regret_observation_2
-- name    : BanditGD.Regret.observation_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T08:05:00.362021+00:00
-- url     : https://prove2.me/theorems/fe11beea-ed40-43f8-84b1-460d6d680a2c
-- title:
--   Observation 2, p. 8 — the ball of radius αr around a point of (1−α)S lies in S
-- statement:
--   Let $S\subseteq\mathbb R^d$ be convex and contain the closed ball $r\mathbb B$ of radius $r>0$ around the origin, and let $0\le\alpha\le1$. Then for every $x\in(1-\alpha)S$,
--   $$\{z\in\mathbb R^d : |z-x|\le\alpha r\}\subseteq S .$$
--
--   This is why the algorithm projects onto $(1-\alpha)S$: perturbing a point of the shrunk set by at most $\alpha r$ never leaves $S$.
-- source:
--   Flaxman, Kalai, McMahan, arXiv:cs/0408007v1, p. 8, Observation 2

import Mathlib
open scoped Pointwise

namespace BanditGD.Regret

theorem observation_2 {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ x ∈ (1 - α) • S, Metric.closedBall x (α * r) ⊆ S := by sorry

end BanditGD.Regret
