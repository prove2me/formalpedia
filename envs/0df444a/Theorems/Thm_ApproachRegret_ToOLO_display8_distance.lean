-- Prove2me | Theorems.Thm_ApproachRegret_ToOLO_display8_distance
-- name    : ApproachRegret.ToOLO.display8_distance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T03:22:36.356274+00:00
-- url     : https://prove2.me/theorems/11eb8769-0a8e-4824-8d3c-34b6a43f01a9
-- title:
--   Display (8) — distance to Algorithm 1’s target
-- statement:
--   Let $K\subseteq\mathbb R^d$ be nonempty, compact, and convex, with $\kappa=\max_{x\in K}\|x\|>0$. Let $S=\operatorname{cone}(\{\kappa\}\times K)^0$. For every $z\in\mathbb R^{d+1}$,
--
--   $$\operatorname{dist}(z,S)=\max_{w\in\operatorname{cone}(\{\kappa\}\times K)\cap B_2(1)}\langle z,w\rangle.$$
--
--   The maximum is attained. Substituting the average payoff of Algorithm 1 yields the paper's displayed identity for its approachability rate.
--
--   **Formalization Note** The display's $\operatorname{cone}(\kappa\oplus K)$ means the cone of the lifted set $\{\kappa\}\times K$; its ball is in $\mathbb R^{d+1}$, although the display labels it with dimension $d$.
-- source:
--   Abernethy, Bartlett, Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, JMLR W&CP 19, https://proceedings.mlr.press/v19/abernethy11b.html, proof of Theorem 16, display (8), p. 37 (PDF p. 11)

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne

open scoped RealInnerProductSpace

namespace ApproachRegret.ToOLO

/-- Display (8), p. 37, for an arbitrary point in the lifted Euclidean space. -/
theorem display8_distance {d : ℕ} (K : Set (E d)) (z : E (d + 1))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hk : 0 < kappa K) :
    IsGreatest ((fun w : E (d + 1) => ⟪z, w⟫) ''
      (cone (lift (kappa K) '' K) ∩ Metric.closedBall 0 1))
      (Metric.infDist z (target K)) := by sorry

end ApproachRegret.ToOLO
