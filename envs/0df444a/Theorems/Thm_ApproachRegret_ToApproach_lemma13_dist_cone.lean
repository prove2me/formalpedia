-- Prove2me | Theorems.Thm_ApproachRegret_ToApproach_lemma13_dist_cone
-- name    : ApproachRegret.ToApproach.lemma13_dist_cone
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:27:19.929973+00:00
-- url     : https://prove2.me/theorems/66f63fb9-d367-4e55-9683-bd76bbd9cd26
-- title:
--   Lemma 13 — the distance to a convex cone is the maximum of ⟨θ, x⟩ over C⁰ ∩ B₂(1)
-- statement:
--   Let $C\subseteq\mathbb R^d$ be a nonempty convex cone, i.e. closed under multiplication by nonnegative scalars and under addition, and let $C^0=\{\theta:\langle\theta,z\rangle\le0\ \forall z\in C\}$ be its polar cone. Then for every $x\in\mathbb R^d$ the maximum below is attained and
--   $$\mathtt{dist}(x,C)=\max_{\theta\in C^0\cap B_2(1)}\langle\theta,x\rangle ,$$
--   where $\mathtt{dist}(x,C)=\inf_{z\in C}\|x-z\|$ and $B_2(1)$ is the closed Euclidean unit ball.
--
--   This dual formula for the distance to a cone is what turns the approachability rate into a linear optimization over $C^0\cap B_2(1)$, the decision set of the online linear optimization algorithm in Algorithm 2.
--
--   **Formalization Note** The statement is `IsGreatest`: $\mathtt{dist}(x,C)$ is a value $\langle\theta,x\rangle$ with $\theta\in C^0\cap B_2(1)$ and an upper bound for all such values. Nonemptiness of $C$ is added: the empty set is a convex cone under Definition 11, and for it the identity fails ($\mathtt{dist}(x,\emptyset)=0$ in Mathlib, while the maximum is $\|x\|$). $C$ is not assumed closed, as on the page.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Lemma 13, eq. (3), p. 35

import Mathlib
import Definitions.Def_ApproachRegret_ToApproach_Setup

open scoped RealInnerProductSpace

namespace ApproachRegret.ToApproach

theorem lemma13_dist_cone {d : ℕ} (C : Set (ApproachRegret.ToOLO.E d)) (hC : IsConvexCone C) (hCne : C.Nonempty)
    (x : ApproachRegret.ToOLO.E d) :
    IsGreatest ((fun θ : ApproachRegret.ToOLO.E d => ⟪θ, x⟫) '' (ApproachRegret.ToOLO.polar C ∩ Metric.closedBall 0 1))
      (Metric.infDist x C) := by sorry

end ApproachRegret.ToApproach
