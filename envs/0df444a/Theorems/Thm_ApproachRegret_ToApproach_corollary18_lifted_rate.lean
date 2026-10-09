-- Prove2me | Theorems.Thm_ApproachRegret_ToApproach_corollary18_lifted_rate
-- name    : ApproachRegret.ToApproach.corollary18_lifted_rate
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T15:28:02.85099+00:00
-- url     : https://prove2.me/theorems/64aa9eb2-12aa-4c60-8dc3-a9190aff45fc
-- title:
--   Corollary 18 — Algorithm 2 on the lifted instance approaches a compact S at rate 2·Regret_T/T
-- statement:
--   Let $(\mathcal X,\mathcal Y,u,S)$ be a Blackwell instance with $S\subseteq\mathbb R^d$ nonempty, compact and convex. Let $\kappa=\max_{s\in S}\|s\|$ and form the lifted instance $(\mathcal X,\mathcal Y,u',S')$ with
--   $$u'(x,y)=\kappa\oplus u(x,y)\in\mathbb R^{d+1},\qquad S'=\mathtt{cone}(\{\kappa\}\times S)\subseteq\mathbb R^{d+1}.$$
--   Let $\mathcal O'$ be a valid halfspace oracle for the lifted instance, let $\mathcal K'=(S')^0\cap B_2(1)$, and let $\mathcal L$ be an online linear optimization algorithm with values in $\mathcal K'$. For $T\ge1$ and any $y_1,\dots,y_T\in\mathcal Y$, run Algorithm 2 on the lifted instance: $\theta_t=\mathcal L(f_1,\dots,f_{t-1})$, $x_t=\mathcal O'(\{z:\langle\theta_t,z\rangle\le0\})$, $f_t=-u'(x_t,y_t)$. Then
--   $$\mathtt{dist}\Big(\frac1T\sum_{t=1}^T u(x_t,y_t),S\Big)\ \le\ 2\,\mathtt{dist}\Big(\frac1T\sum_{t=1}^T u'(x_t,y_t),S'\Big)\ \le\ \frac2T\,\mathrm{Regret}_T,$$
--   where $\mathrm{Regret}_T=\sum_{t=1}^T\langle f_t,\theta_t\rangle-\min_{\theta\in\mathcal K'}\sum_{t=1}^T\langle f_t,\theta\rangle$ is the regret of $\mathcal L$ on the lifted losses.
--
--   Consequently any no-regret online linear optimization algorithm, together with a valid halfspace oracle, yields an approachability algorithm for every compact convex target set, at rate twice the average regret.
--
--   **Formalization Note** The page writes $\mathrm{Regret}_T(\mathcal A)$; the quantity is the regret of the OLO algorithm $\mathcal L$ on the decision set $\mathcal K'$ against the losses $f_t=-u'(x_t,y_t)$, as in Theorem 17. The oracle is a valid oracle for the lifted instance, which is the input "a valid halfspace oracle" of Algorithm 2 when it is applied to $(\mathcal X,\mathcal Y,u',S')$. Added: $S\ne\emptyset$ (so that $\kappa$ is a maximum) and $T\ge1$. The run is given by hypotheses on sequences indexed by $t=1,\dots,T$; it exists and is unique by recursion. The two inequalities are stated as a conjunction, keeping the middle term.
-- source:
--   Abernethy, Bartlett, Hazan (COLT 2011, JMLR W&CP 19), Corollary 18, p. 39 (with Algorithm 2 and Theorem 17, p. 38)

import Mathlib
import Definitions.Def_ApproachRegret_ToApproach_Setup

open scoped RealInnerProductSpace

namespace ApproachRegret.ToApproach

theorem corollary18_lifted_rate {n m d : ℕ} (X : Set (ApproachRegret.ToOLO.E n)) (Y : Set (ApproachRegret.ToOLO.E m))
    (u : ApproachRegret.ToOLO.E n → ApproachRegret.ToOLO.E m → ApproachRegret.ToOLO.E d) (S : Set (ApproachRegret.ToOLO.E d)) (hInst : IsBlackwellInstance X Y u S)
    (hScpt : IsCompact S) (hSne : S.Nonempty)
    (O' : ApproachRegret.ToOLO.E (d + 1) → ℝ → ApproachRegret.ToOLO.E n)
    (hO' : IsValidOracle X Y (liftedPayoff (setNorm S) u) (liftedSet S) O')
    (L : (t : ℕ) → (Fin t → ApproachRegret.ToOLO.E (d + 1)) → ApproachRegret.ToOLO.E (d + 1))
    (hL : ∀ t h, L t h ∈ ApproachRegret.ToOLO.polar (liftedSet S) ∩ Metric.closedBall 0 1)
    (y : ℕ → ApproachRegret.ToOLO.E m) (T : ℕ) (hT : 1 ≤ T) (hy : ∀ t, 1 ≤ t → t ≤ T → y t ∈ Y)
    (θ : ℕ → ApproachRegret.ToOLO.E (d + 1)) (x : ℕ → ApproachRegret.ToOLO.E n) (f : ℕ → ApproachRegret.ToOLO.E (d + 1))
    (hrun : IsAlg2Run (liftedPayoff (setNorm S) u) O' L y T θ x f) :
    Metric.infDist (avgPayoff u x y T) S ≤
        2 * Metric.infDist (avgPayoff (liftedPayoff (setNorm S) u) x y T) (liftedSet S) ∧
      2 * Metric.infDist (avgPayoff (liftedPayoff (setNorm S) u) x y T) (liftedSet S) ≤
        2 / T * regret (ApproachRegret.ToOLO.polar (liftedSet S) ∩ Metric.closedBall 0 1) θ f T := by sorry

end ApproachRegret.ToApproach
