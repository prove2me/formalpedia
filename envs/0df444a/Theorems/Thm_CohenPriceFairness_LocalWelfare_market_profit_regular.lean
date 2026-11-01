-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_market_profit_regular
-- name    : CohenPriceFairness.LocalWelfare.market_profit_regular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:33.492322+00:00
-- url     : https://prove2.me/theorems/4f28088e-12a4-4a65-880d-635a76651180
-- title:
--   General valuations: local regularity at a nondegenerate optimum
-- statement:
--   Throughout, a market has two groups $i\in\{0,1\}$ with masses $d_i>0$, cost $c\ge0$ and valuation laws $\mu_i$; $\bar F_i(p)=\mu_i([p,\infty))$ is the purchase probability, $R_i(p)=d_i(p-c)\bar F_i(p)$ the profit, $S_i(p)=\int(v-p)^+\,d\mu_i$ the surplus and $N_i(p)$ the mean valuation of non-buyers. For a fairness measure $M_i\in\{p,\bar F_i,S_i,N_i\}$, a *sensitivity claim* $\mathrm{SC}(b,M,C)$ at baseline prices $b$ says: a selection $\alpha\mapsto p(\alpha)$ of optimal prices of the fairness-constrained problem $\max R_0(p_0)+R_1(p_1)$ s.t. $|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|M_0(b_0)-M_1(b_1)|$ with $p(0)=b$ exists on some $[0,\varepsilon]$, and for every such selection the welfare $\mathcal W(\alpha)=\sum_i R_i(p_i(\alpha))+d_iS_i(p_i(\alpha))$ has a finite right derivative $D$ at $0$ with $C(D)$.
--
--   Let the market be admissible (nonnegative valuation laws with finite mean, positive masses, $c\ge0$), let $b$ be unconstrained optimal prices satisfying the regularity of Lemma 1 (twice differentiability of $\bar F_i,S_i,N_i,R_i$ at $b_i$, local monotone invertibility), and suppose each $b_i$ is the unique maximiser of $R_i$ on $[0,\infty)$. Then (i) every $b_i>0$; (ii) near-optimal prices are localised: for every $\varepsilon>0$ there is $\delta>0$ with $R_i(p)\ge R_i(b_i)-\delta\Rightarrow|p-b_i|<\varepsilon$ for $p\ge0$; (iii) each $R_i$ is continuous near $b_i$; (iv) $R_i(b_i+h)=R_i(b_i)+\tfrac{r_i}{2}h^2+o(h^2)$; (v) $S_i'(b_i)=-\bar F_i(b_i)$ with $r_i=R_i''(b_i)$, and $\bar F_i(b_i)>0$.
--
--   It isolates one step of the proof of Lemma 1 (Online Appendix A, pp. 31–33).
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; Online Appendix A, Lemma 1 and its proof, pp. 30-33.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare

theorem market_profit_regular (m : Market) (hm : m.Admissible) (b : Prices)
    (hb : BaselineOptimal m b) (hr : LemmaRegularity m b)
    (huniq : ∀ i, ∀ p : ℝ, 0 ≤ p → profit m i (b i) ≤ profit m i p → p = b i) :
    (∀ i, 0 < b i) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε) ∧
      (∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η))) ∧
      (∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - deriv (deriv (profit m i)) (b i) / 2 * h ^ 2)
        =o[𝓝 0] (fun h => h ^ 2)) ∧
      (∀ i, HasDerivAt (surplus m i) (-demand m i (b i)) (b i)) ∧
    (∀ i, 0 < demand m i (b i)) := by sorry

end CohenPriceFairness.LocalWelfare
