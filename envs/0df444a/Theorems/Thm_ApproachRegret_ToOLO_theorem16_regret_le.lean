-- Prove2me | Theorems.Thm_ApproachRegret_ToOLO_theorem16_regret_le
-- name    : ApproachRegret.ToOLO.theorem16_regret_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T03:22:30.902992+00:00
-- url     : https://prove2.me/theorems/ef6eff68-eeb1-4ba5-8c72-80a800c2d84b
-- title:
--   Theorem 16 — approachability rate bounds OLO regret
-- statement:
--   Let $K\subseteq\mathbb R^d$ be nonempty, compact, and convex, and set $\kappa=\max_{x\in K}\|x\|>0$. Feed each loss vector $f_t\in B_2(1)$ to any algorithm $A$ that selects a point of $K$ from past admissible losses. Algorithm 1 uses that same decision as its OLO decision and evaluates it in the lifted Blackwell instance. For every horizon $T\ge1$,
--
--   $$\frac{\operatorname{Regret}_T(A;f_{1:T})}{T}\le 2\kappa\,D_T(A;f_{1:T}),$$
--
--   where $D_T$ is the Euclidean distance of the average vector payoff to Algorithm 1's target. The bound transfers a finite-horizon approachability guarantee to regret.
--
--   **Formalization Note** The source's division by $\kappa$ requires $\kappa>0$; the zero-set case has zero regret but an undefined source instance. Histories and sums use rounds $1,\ldots,T$. No approachability-rate hypothesis is imposed on $A$.
-- source:
--   Abernethy, Bartlett, Hazan, Blackwell Approachability and No-Regret Learning are Equivalent, COLT 2011, JMLR W&CP 19, https://proceedings.mlr.press/v19/abernethy11b.html, Theorem 16, p. 37 (PDF p. 11); proof ends p. 38 (PDF p. 12)

import Mathlib
import Definitions.Def_ApproachRegret_ToOLO_AlgorithmOne

open scoped RealInnerProductSpace

namespace ApproachRegret.ToOLO

/-- Theorem 16, p. 37: Algorithm 1 converts any approachability algorithm into OLO. -/
theorem theorem16_regret_le {d : ℕ} (K : Set (E d))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (hk : 0 < kappa K)
    (A : (n : ℕ) → (Fin n → E d) → E d)
    (hA : ∀ n (h : Fin n → E d),
      (∀ i, h i ∈ Metric.closedBall (0 : E d) 1) → A n h ∈ K)
    (f : ℕ → E d) (T : ℕ) (hT : 1 ≤ T)
    (hf : ∀ t, 1 ≤ t → t ≤ T → f t ∈ Metric.closedBall (0 : E d) 1) :
    regret K A f T / (T : ℝ) ≤
      2 * kappa K * approachRate K A f T := by sorry

end ApproachRegret.ToOLO
