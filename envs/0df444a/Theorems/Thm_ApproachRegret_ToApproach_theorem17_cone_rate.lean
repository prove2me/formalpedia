-- Prove2me | Theorems.Thm_ApproachRegret_ToApproach_theorem17_cone_rate
-- name    : ApproachRegret.ToApproach.theorem17_cone_rate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T15:27:41.812982+00:00
-- url     : https://prove2.me/theorems/483e1fd0-8b15-49a8-8a23-b2cb19d7d038
-- title:
--   Theorem 17 — when S is a cone, Algorithm 2 approaches S at rate Regret(L_K; f_{1:T})/T
-- statement:
--   Let $(\mathcal X,\mathcal Y,u,S)$ be a Blackwell instance (compact convex $\mathcal X\subseteq\mathbb R^n$, $\mathcal Y\subseteq\mathbb R^m$, $u$ biaffine on $\mathcal X\times\mathcal Y$, $S\subseteq\mathbb R^d$ closed and convex) in which $S$ is a cone, and let $\mathcal O$ be a valid halfspace oracle for it. Put $\mathcal K=S^0\cap B_2(1)$ and let $\mathcal L$ be an online linear optimization algorithm with values in $\mathcal K$. Let $T\ge1$, let $y_1,\dots,y_T\in\mathcal Y$ be arbitrary, and run Algorithm 2: for $t=1,\dots,T$,
--   $$\theta_t=\mathcal L(f_1,\dots,f_{t-1}),\qquad x_t=\mathcal O(H_{\theta_t}),\ H_{\theta_t}=\{z:\langle\theta_t,z\rangle\le0\},\qquad f_t=-u(x_t,y_t).$$
--   Then
--   $$\mathtt{dist}\Big(\frac1T\sum_{t=1}^T u(x_t,y_t),\,S\Big)\ \le\ \frac{\mathrm{Regret}(\mathcal L_{\mathcal K};f_{1:T})}{T},$$
--   where $\mathrm{Regret}(\mathcal L_{\mathcal K};f_{1:T})=\sum_{t=1}^T\langle f_t,\theta_t\rangle-\min_{\theta\in\mathcal K}\sum_{t=1}^T\langle f_t,\theta\rangle$.
--
--   Thus any no-regret algorithm on $S^0\cap B_2(1)$, combined with a valid halfspace oracle, is an approachability algorithm for a conic target set, with the same rate.
--
--   **Formalization Note** The run is given by hypotheses on sequences $\theta,x,f$ indexed by $t=1,\dots,T$; such sequences exist and are unique, by recursion on $t$. The oracle is valid for every halfspace containing $S$ (encoded as $(a,c)$), not only for those queried. $1\le T$ is added. $S$ is not assumed nonempty: the statement holds without it.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Algorithm 2 and Theorem 17, p. 38

import Mathlib
import Definitions.Def_ApproachRegret_ToApproach_Setup

open scoped RealInnerProductSpace

namespace ApproachRegret.ToApproach

theorem theorem17_cone_rate {n m d : ℕ} (X : Set (ApproachRegret.ToOLO.E n)) (Y : Set (ApproachRegret.ToOLO.E m))
    (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d) (S : Set (ApproachRegret.ToOLO.E d)) (hInst : IsBlackwellInstance X Y u S)
    (hcone : IsCone S) (O : ApproachRegret.ToOLO.E d → ℝ → ApproachRegret.ToOLO.E n) (hO : IsValidOracle X Y u S O)
    (L : (t : ℕ) → (Fin t → ApproachRegret.ToOLO.E d) → ApproachRegret.ToOLO.E d)
    (hL : ∀ t h, L t h ∈ ApproachRegret.ToOLO.polar S ∩ Metric.closedBall 0 1)
    (y : ℕ → ApproachRegret.ToOLO.E m) (T : ℕ) (hT : 1 ≤ T) (hy : ∀ t, 1 ≤ t → t ≤ T → y t ∈ Y)
    (θ : ℕ → ApproachRegret.ToOLO.E d) (x : ℕ → ApproachRegret.ToOLO.E n) (f : ℕ → ApproachRegret.ToOLO.E d) (hrun : IsAlg2Run u O L y T θ x f) :
    Metric.infDist (avgPayoff u x y T) S ≤
      regret (ApproachRegret.ToOLO.polar S ∩ Metric.closedBall 0 1) θ f T / T := by sorry

end ApproachRegret.ToApproach
