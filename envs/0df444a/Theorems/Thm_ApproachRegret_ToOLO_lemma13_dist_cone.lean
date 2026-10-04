-- Prove2me | Theorems.Thm_ApproachRegret_ToOLO_lemma13_dist_cone
-- name    : ApproachRegret.ToOLO.lemma13_dist_cone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:00:38.614844+00:00
-- url     : https://prove2.me/theorems/e7dbeeb8-5992-4ff0-bb55-b2c05f28ca3e
-- title:
--   Lemma 13 — distance to a convex cone
-- statement:
--   Let $C\subseteq\mathbb R^d$ be a nonempty convex cone, and let $x\in\mathbb R^d$. With $C^0$ the polar defined by nonpositive inner products and $B_2(1)$ the Euclidean unit ball,
--
--   $$\operatorname{dist}(x,C)=\max_{\theta\in C^0\cap B_2(1)}\langle\theta,x\rangle.$$
--
--   The maximum is attained. This identity converts a geometric distance into a linear optimization over a polar cone.
--
--   **Formalization Note** Nonemptiness is explicit because Definition 11 permits the empty cone, while the source's distance formula does not cover that case. Closedness is not assumed.
-- source:
--   Abernethy, Bartlett, Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, JMLR W&CP 19, https://proceedings.mlr.press/v19/abernethy11b.html, Lemma 13, p. 35 (PDF p. 9), equation (3)

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_Cones

open scoped RealInnerProductSpace

namespace ApproachRegret.ToOLO

/-- Lemma 13, p. 35, including attainment of the maximum. -/
theorem lemma13_dist_cone {d : ℕ} (C : Set (E d)) (x : E d)
    (hC : Convex ℝ C) (hcone : ∀ z ∈ C, ∀ α : ℝ, 0 ≤ α → α • z ∈ C)
    (hne : C.Nonempty) :
    IsGreatest ((fun θ : E d => ⟪θ, x⟫) ''
      (polar C ∩ Metric.closedBall 0 1)) (Metric.infDist x C) := by sorry

end ApproachRegret.ToOLO
