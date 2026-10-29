-- Prove2me | Theorems.Thm_ChenChaoShiSALA_Regret_proposition_3
-- name    : ChenChaoShiSALA.Regret.proposition_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T05:20:25.125999+00:00
-- url     : https://prove2.me/theorems/a06ec8f0-cc91-4038-a822-aeb467bbf1be
-- title:
--   Proposition 3 — printed safety-stock estimation
-- statement:
--   Let $P=[p^l,p^h]$ be the real price interval, $b\ge0$ and $h>0$ the shortage and holding costs, with $b+p>0$ on $P$. The nonincreasing demand-price function is $\lambda$, and errors $\epsilon_t$ are independent measurable variables with a common real probability law $\nu$, mean zero and finite standard deviation $\sigma$. Its CDF $F$ is differentiable and its density is $f=F'$. Fix positive constants $A,M,\theta_1,\theta_2,\theta_3,\kappa,r,a$. Demand is nonincreasing on $[p^l-A,p^h+A]$; $f(x)\le\theta_1e^{-\theta_2x}$ for $x\ge\theta_3$; and $f(x)\ge r$ within $\kappa$ of $z^*(p)=F^{-1}((b+p)/(b+p+h))$ for each $p\in P$. Let $Q$ be the expected period profit (1), $G(p)=\max_{y\in\mathbb R}Q(p,y)$, and $(p^*,y^*)$ its continuous-price optimal pair, with $p^*$ interior and $G''\le-a$ on $P$. The quantile is the lower generalized inverse.
--
--   At horizon $T$, use Algorithm 1 with all three ceilings in (7), $\mu=1$, $N=L(m+l)m$, exploration level $B=\lceil\log L\log\log L\rceil$, and grid spacing $\Delta=T^{-1/4}$. Require only its construction domain: $T\ge3$, $L>1$, $l\ge1$, $N\le T$, and all extension knots in $[p^l-A,p^h+A]$. For exactly the derivative orders $0,\ldots,m=\max(3,\lceil\sqrt{\log T}\rceil)$, derivatives of $\lambda$ exist on that interval and have absolute value at most $M$. Observed exploration sales are $\min(\lambda(p_t)+\epsilon_t,B)$; $\widehat\lambda$ is their explicit Algorithm 0 spline, and $\eta_t$ are the block-centered residuals. The grid includes the upper endpoint. $(\widehat p,\widehat y)$ maximizes the sample-average profit over the grid and every real inventory level, taking the least price and least inventory in a tie. The printed $\widehat z(p)$ uses the unnormalized count of residuals, distinct from this optimizer's normalized empirical quantile. All probabilities below are under the probability measure carrying the error sequence.
--
--   For each fixed $p\in P$, with $K_3=1/r+\sigma$ and the literal unnormalized-count $\widehat z$ printed on page 16,
--   $$\mathbb P\{|z^*(p)-\widehat z(p)|\le K_3T^{-1/4}\}>1-4T^{-2}.$$
--
--   Differences from the source:
--   - encoding: periods indexed from 1 and real probability notation → zero-based finite sums and the real value of a probability measure; reason: exact reindexing with unchanged probabilities
--   - reading: costs and inverse-CDF domain implicit in the economic model → h > 0, b ≥ 0 and b+p > 0 on the price interval; reason: the stated economic and strictly-interior critical-ratio conventions
--   - encoding: Algorithm 1 is used on its defined exploration/exploitation horizon → T ≥ 3, L > 1, l ≥ 1, N ≤ T and extension knots in the smoothness interval; reason: deterministic construction conditions only; no accuracy event or asymptotic error threshold
--   - reading: grid ellipsis ends at the upper price and optimizer ties are unspecified → include the upper endpoint and select the least optimizing price and inventory; reason: make the grid boundary and algorithm a deterministic function of observed sales
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, p. 16, Proposition 3; p. 15, Remark 1

import Definitions.Def_ChenChaoShiSALA_Regret_Spline
import Definitions.Def_ChenChaoShiSALA_Regret_Model
import Definitions.Def_ChenChaoShiSALA_Regret_Parameters
import Definitions.Def_ChenChaoShiSALA_Regret_Observations
import Definitions.Def_ChenChaoShiSALA_Regret_Algorithm

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace ChenChaoShiSALA.Regret

theorem proposition_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : Market) (c : Constants) (hs : Standing e c) (T : ℕ)
    (hd : ConstructionDomain e c T) (hsm : HorizonSmooth e c T)
    (err : ℕ → Ω → ℝ) (hn : NoiseSequence μ e err) :
    ∀ p ∈ e.prices,
      (μ {ω | |e.stock p - printedStock e T (explorationSales e T (fun t => err t ω)) p| ≤
        (1 / c.r + e.sigma) * (T : ℝ) ^ (-(1 / 4 : ℝ))}).toReal >
      1 - 4 * (T : ℝ) ^ (-(2 : ℝ)) := by sorry

end ChenChaoShiSALA.Regret
