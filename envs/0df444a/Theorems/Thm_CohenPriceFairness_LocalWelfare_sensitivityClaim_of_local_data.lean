-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_local_data
-- name    : CohenPriceFairness.LocalWelfare.sensitivityClaim_of_local_data
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:14:01.332782+00:00
-- url     : https://prove2.me/theorems/adec5a53-1a59-4769-929f-bfe8d0c6bbdb
-- title:
--   Sensitivity claim from local data at the baseline
-- statement:
--   Throughout, a market has two groups $i\in\{0,1\}$ with masses $d_i>0$, cost $c\ge0$ and valuation laws $\mu_i$; $\bar F_i(p)=\mu_i([p,\infty))$ is the purchase probability, $R_i(p)=d_i(p-c)\bar F_i(p)$ the profit, $S_i(p)=\int(v-p)^+\,d\mu_i$ the surplus and $N_i(p)$ the mean valuation of non-buyers. For a fairness measure $M_i\in\{p,\bar F_i,S_i,N_i\}$, a *sensitivity claim* $\mathrm{SC}(b,M,C)$ at baseline prices $b$ says: a selection $\alpha\mapsto p(\alpha)$ of optimal prices of the fairness-constrained problem $\max R_0(p_0)+R_1(p_1)$ s.t. $|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|M_0(b_0)-M_1(b_1)|$ with $p(0)=b$ exists on some $[0,\varepsilon]$, and for every such selection the welfare $\mathcal W(\alpha)=\sum_i R_i(p_i(\alpha))+d_iS_i(p_i(\alpha))$ has a finite right derivative $D$ at $0$ with $C(D)$.
--
--   Let $b$ be baseline prices with $b_i>0$ maximising each $R_i$ on $[0,\infty)$, with localisation of near-optimal prices, continuity of $R_i$ and $M_i$ near $b_i$, an expansion $R_i(b_i+h)=R_i(b_i)+\tfrac{r_i}{2}h^2+o(h^2)$ with $r_i<0$, derivatives $M_i'(b_i)=m_i$ not both zero, $S_i'(b_i)=\sigma_i$, and $M_0(b_0)\ne M_1(b_1)$. With $K=m_0^2/r_0+m_1^2/r_1$ and $\mu=-(M_0(b_0)-M_1(b_1))/K$, define
--   $$D^*=d_0\sigma_0\frac{\mu m_0}{r_0}-d_1\sigma_1\frac{\mu m_1}{r_1}.$$
--   If $C(D^*)$ holds, then the sensitivity claim $\mathrm{SC}(b,M,C)$ holds.
--
--   This translates the general perturbation theorem into the market language of the mission (Problem (1), p. 4, and footnote 7, p. 7): it produces both the existence of a local optimal selection and the finite right derivative $D^*$ for every selection. All eight family/metric cases of Theorem 2 and all four parts of Lemma 1 are obtained from it.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; Problem (1), p. 4, footnote 7, p. 7; Online Appendix A, proof of Lemma 1, pp. 31-33.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare

theorem sensitivityClaim_of_local_data (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop)
    (r mm σ : Fin 2 → ℝ)
    (hb : ∀ i, 0 < b i)
    (hopt : ∀ i, ∀ p, 0 ≤ p → profit m i p ≤ profit m i (b i))
    (hloc : ∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p →
      |p - b i| < ε)
    (hcont : ∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η)) ∧
      ContinuousOn (metricValue m k i) (Set.Icc (b i - η) (b i + η)))
    (hr : ∀ i, r i < 0)
    (hRt : ∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - r i / 2 * h ^ 2)
      =o[𝓝 0] (fun h => h ^ 2))
    (hMd : ∀ i, HasDerivAt (metricValue m k i) (mm i) (b i))
    (hmm : mm 0 ≠ 0 ∨ mm 1 ≠ 0)
    (hSd : ∀ i, HasDerivAt (surplus m i) (σ i) (b i))
    (hgap : metricValue m k 0 (b 0) ≠ metricValue m k 1 (b 1))
    (hC : C (m.population 0 * σ 0 * ((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 0 / r 0) +
      m.population 1 * σ 1 * (-((-(metricValue m k 0 (b 0) - metricValue m k 1 (b 1)) /
        (mm 0 ^ 2 / r 0 + mm 1 ^ 2 / r 1)) * mm 1 / r 1)))) :
    SensitivityClaim m b k C := by sorry

end CohenPriceFairness.LocalWelfare
