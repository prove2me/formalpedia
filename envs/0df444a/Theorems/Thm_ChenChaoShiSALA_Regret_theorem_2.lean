-- Prove2me | Theorems.Thm_ChenChaoShiSALA_Regret_theorem_2
-- name    : ChenChaoShiSALA.Regret.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:19:57.348992+00:00
-- url     : https://prove2.me/theorems/05937f48-bfc3-4690-8a52-32888a4cdd11
-- title:
--   Theorem 2 — nearly square-root cumulative regret of SALA
-- statement:
--   Let $P=[p^l,p^h]$ be the real price interval, $b\ge0$ and $h>0$ the shortage and holding costs, with $b+p>0$ on $P$. The nonincreasing demand-price function is $\lambda$, and errors $\epsilon_t$ are independent measurable variables with a common real probability law $\nu$, mean zero and finite standard deviation $\sigma$. Its CDF $F$ is differentiable and its density is $f=F'$. Fix positive constants $A,M,\theta_1,\theta_2,\theta_3,\kappa,r,a$. Demand is nonincreasing on $[p^l-A,p^h+A]$; $f(x)\le\theta_1e^{-\theta_2x}$ for $x\ge\theta_3$; and $f(x)\ge r$ within $\kappa$ of $z^*(p)=F^{-1}((b+p)/(b+p+h))$ for each $p\in P$. Let $Q$ be the expected period profit (1), $G(p)=\max_{y\in\mathbb R}Q(p,y)$, and $(p^*,y^*)$ its continuous-price optimal pair, with $p^*$ interior and $G''\le-a$ on $P$. The quantile is the lower generalized inverse.
--
--   For each horizon use the concrete censored-data Algorithm 1 described above, with $m=\max(3,\lceil\sqrt{\log T}\rceil)$, $L=\lceil T^{1/2+1/(\log T)^{1/3}}\rceil$, $l=\lceil(\log T)^{3/2}T^{1/(4\sqrt{\log T})}\rceil$, $N=L(m+l)m$, $B=\lceil\log L\log\log L\rceil$, and $\Delta=T^{-1/4}$. Exploration uses its exact fixed inventory target, residuals are centered by their block mean, and exploitation uses $y_t=\max(x_t,\widehat y)$ with the actual recursively carried inventory. Recommendations maximize the empirical profit over grid prices and all real inventories; the endpoint is included and ties use least price and least inventory. Define the cumulative expected regret by (3),
--   $$R^{\mathrm{SALA}}(T)=TQ(p^*,y^*)-\mathbb E\sum_{t=1}^T Q(p_t,y_t).$$
--   Set $\varepsilon(T)=(\log T)^{-1/3}+1/(4\sqrt{\log T})$. Then $\varepsilon(T)\to0$, and there is a threshold $T_0\ge3$ depending only on the fixed market and constants, chosen before $T$ and the noise realization or probability-space representation. For every $T\ge T_0$, the deterministic construction domain holds: $L>1$, $l\ge1$, $N\le T$ and every extension knot lies in $[p^l-A,p^h+A]$. If the derivatives of orders $0,\ldots,m(T)$ exist on that interval and are bounded in absolute value by the same fixed $M$, then for every probability space carrying the stated i.i.d. error law,
--   $$R^{\mathrm{SALA}}(T)\le(b+p^h+h)T^{1/2+\varepsilon(T)}(\log T)^3\log\log T.$$
--   This is an eventual bound with the explicit constant and exponent from Remark 1 and the discussion on page 15; it does not require an analytic demand function or assume accurate learning.
--
--   Differences from the source:
--   - encoding: periods indexed from 1 and real probability notation → zero-based finite sums and the real value of a probability measure; reason: exact reindexing with unchanged probabilities
--   - reading: costs and inverse-CDF domain implicit in the economic model → h > 0, b ≥ 0 and b+p > 0 on the price interval; reason: the stated economic and strictly-interior critical-ratio conventions
--   - reading: grid ellipsis ends at the upper price and optimizer ties are unspecified → include the upper endpoint and select the least optimizing price and inventory; reason: make the grid boundary and algorithm a deterministic function of observed sales
--   - reading: average regret in Theorem 2 → the cumulative regret defined in equation (3); reason: the definition and proof both use the unnormalized sum
--   - encoding: large T with ε arbitrarily small; finite-order Assumption 1(ii) → a model-dependent threshold, ε(T) tending to zero and horizonwise smoothness after the threshold; reason: retain the explicit page-15 exponent without imposing infinite smoothness or allowing a horizon-dependent constant
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, p. 14, Theorem 2; p. 15, Remark 1

import Definitions.Def_ChenChaoShiSALA_Regret_Spline
import Definitions.Def_ChenChaoShiSALA_Regret_Model
import Definitions.Def_ChenChaoShiSALA_Regret_Parameters
import Definitions.Def_ChenChaoShiSALA_Regret_Observations
import Definitions.Def_ChenChaoShiSALA_Regret_Algorithm

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace ChenChaoShiSALA.Regret

theorem theorem_2 (e : Market) (c : Constants) (hs : Standing e c) :
    Filter.Tendsto (fun T : ℕ => epsilon T) Filter.atTop (𝓝 0) ∧
    ∃ T0 : ℕ, 3 ≤ T0 ∧ ∀ T ≥ T0,
      ConstructionDomain e c T ∧
      (HorizonSmooth e c T →
        ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
          (err : ℕ → Ω → ℝ), NoiseSequence μ e err →
          regret μ e T err ≤ (e.b + e.high + e.h) *
            (T : ℝ) ^ ((1 / 2 : ℝ) + epsilon T) *
            (Real.log T) ^ 3 * Real.log (Real.log T)) := by sorry

end ChenChaoShiSALA.Regret
