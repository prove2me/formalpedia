-- Prove2me | Theorems.Thm_ApproachRegret_ToApproach_lemma14_lift_dist
-- name    : ApproachRegret.ToApproach.lemma14_lift_dist
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:28:54.002368+00:00
-- url     : https://prove2.me/theorems/2a8b9213-6724-48ba-91ee-e6c93a059d92
-- title:
--   Lemma 14 — lifting K to cone({κ} × K) changes the distance by at most a factor 2
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^d$ be a nonempty compact convex set, let $\kappa=\max_{z\in\mathcal K}\|z\|$, and let $x\in\mathbb R^d$ with $x\notin\mathcal K$. Put $\tilde x=\kappa\oplus x\in\mathbb R^{d+1}$ and $\tilde{\mathcal K}=\{\kappa\}\times\mathcal K=\{\kappa\oplus z: z\in\mathcal K\}$. Then
--   $$\mathtt{dist}\big(\tilde x,\mathtt{cone}(\tilde{\mathcal K})\big)\ \le\ \mathtt{dist}(x,\mathcal K)\ \le\ 2\,\mathtt{dist}\big(\tilde x,\mathtt{cone}(\tilde{\mathcal K})\big).$$
--
--   The lemma lets one replace a compact convex target set by a cone one dimension up while losing at most a factor two in distance; it is how Algorithm 2 is extended from conic to compact target sets (Corollary 18).
--
--   **Formalization Note** $\oplus$ is the Euclidean concatenation, $\|a\oplus z\|^2=a^2+\|z\|^2$. Nonemptiness of $\mathcal K$ is added (it is needed for $\kappa$ to be a maximum). The page writes "$\mathcal K\subseteq\mathcal H$ in $\mathbb R^d$", with a stray symbol $\mathcal H$, and calls $\kappa$ the "diameter", although it defines $\kappa=\max_{x\in\mathcal K}\|x\|$; the norm is used, as defined. The page's hypothesis $x\notin\mathcal K$ is kept.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Lemma 14, eq. (7), p. 35

import Mathlib
import Definitions.Def_ApproachRegret_ToApproach_Setup

open scoped RealInnerProductSpace

namespace ApproachRegret.ToApproach

theorem lemma14_lift_dist {d : ℕ} (K : Set (ApproachRegret.ToOLO.E d)) (hKc : IsCompact K) (hKconv : Convex ℝ K)
    (hKne : K.Nonempty) (x : ApproachRegret.ToOLO.E d) (hx : x ∉ K) :
    Metric.infDist (ApproachRegret.ToOLO.lift (setNorm K) x) (ApproachRegret.ToOLO.cone (ApproachRegret.ToOLO.lift (setNorm K) '' K)) ≤ Metric.infDist x K ∧
      Metric.infDist x K ≤
        2 * Metric.infDist (ApproachRegret.ToOLO.lift (setNorm K) x) (ApproachRegret.ToOLO.cone (ApproachRegret.ToOLO.lift (setNorm K) '' K)) := by sorry

end ApproachRegret.ToApproach
