-- Prove2me | Theorems.Thm_ChenChaoShiSALA_Regret_lemma_1
-- name    : ChenChaoShiSALA.Regret.lemma_1
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-10-29T05:20:07.523981+00:00
-- url     : https://prove2.me/theorems/e3bc9d8c-ffe6-4e7d-81f5-d8fe0ed1eafd
-- title:
--   Lemma 1 — concentration of an independent, non-identical sequence
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be any probability space and $(\zeta_t)_{t\ge1}$ independent measurable real random variables. Each has mean zero and finite second moment, with actual standard deviation $\sigma_t=\sqrt{\mathbb E[\zeta_t^2]}$. Suppose there is a common $\rho>0$ such that $\mathbb E[e^{s\zeta_t}]<\infty$ for every $t$ and every $s\in(-\rho,\rho)$. No identical-distribution or quantitative uniform MGF bound is imposed. For $L\ge1$, let $\sigma_{\max}(L)=\max_{1\le t\le L}\sigma_t$. The printed claim is that there exists $L_0\ge2$ such that every $L\ge L_0$ satisfies
--   $$\mathbb P\left\{\left|\frac1L\sum_{t=1}^L\zeta_t\right|\le4\sigma_{\max}(L)L^{-1/2}\sqrt{\log L}\right\}>1-\frac2{L^4}.$$
--   The threshold is chosen for the fixed infinite sequence, before $L$. This is the source's non-identical concentration claim, retained for proof or disproof.
--
--   Differences from the source:
--   - encoding: periods indexed from 1 and real probability notation → zero-based finite sums and the real value of a probability measure; reason: exact reindexing with unchanged probabilities
--   - reading: finite symbols T,L followed by large enough L; prose ξ but MGF formula ζ → prefixes of one infinite independent sequence and the same ζ in the MGF; reason: give the large-L assertion a nonvacuous meaning and follow its displayed MGF formula
--   - encoding: finite variances and finite MGFs → integrability of each variable, square and MGF exponential; reason: express genuine finite expectations rather than total-integral default values
-- source:
--   Chen, Chao and Shi (2021), Nonparametric Learning Algorithms for Joint Pricing and Inventory Control with Lost Sales and Censored Demand, Mathematics of Operations Research, doi:10.1287/moor.2020.1084, supplied source.pdf, p. 15, Lemma 1

import Definitions.Def_ChenChaoShiSALA_Regret_Spline
import Definitions.Def_ChenChaoShiSALA_Regret_Model
import Definitions.Def_ChenChaoShiSALA_Regret_Parameters
import Definitions.Def_ChenChaoShiSALA_Regret_Observations
import Definitions.Def_ChenChaoShiSALA_Regret_Algorithm

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace ChenChaoShiSALA.Regret

theorem lemma_1 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hm : ∀ t, Measurable (X t)) (hi : iIndepFun X μ)
    (hint : ∀ t, Integrable (X t) μ)
    (hsq : ∀ t, Integrable (fun ω => (X t ω) ^ 2) μ)
    (hc : ∀ t, (∫ ω, X t ω ∂μ) = 0)
    (hmgf : ∃ rho : ℝ, 0 < rho ∧ ∀ t, ∀ s ∈ Set.Ioo (-rho) rho,
      Integrable (fun ω => Real.exp (s * X t ω)) μ) :
    ∃ L0 : ℕ, 2 ≤ L0 ∧ ∀ L ≥ L0,
      (μ {ω | |(∑ t ∈ Finset.range L, X t ω) / (L : ℝ)| ≤
        4 * sSup {v : ℝ | ∃ t < L, v = Real.sqrt (∫ ω, (X t ω) ^ 2 ∂μ)} *
          (L : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt (Real.log L)}).toReal >
        1 - 2 / (L : ℝ) ^ 4 := by sorry

end ChenChaoShiSALA.Regret
