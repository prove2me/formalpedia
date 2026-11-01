-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_profit_regular
-- name    : CohenPriceFairness.LocalWelfare.uniform_profit_regular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:14:21.226505+00:00
-- url     : https://prove2.me/theorems/38f3906d-0679-412a-80af-00675007dd2d
-- title:
--   Uniform valuations: the optimal prices and their local regularity
-- statement:
--   Throughout, a market has two groups $i\in\{0,1\}$ with masses $d_i>0$, cost $c\ge0$ and valuation laws $\mu_i$; $\bar F_i(p)=\mu_i([p,\infty))$ is the purchase probability, $R_i(p)=d_i(p-c)\bar F_i(p)$ the profit, $S_i(p)=\int(v-p)^+\,d\mu_i$ the surplus and $N_i(p)$ the mean valuation of non-buyers. For a fairness measure $M_i\in\{p,\bar F_i,S_i,N_i\}$, a *sensitivity claim* $\mathrm{SC}(b,M,C)$ at baseline prices $b$ says: a selection $\alpha\mapsto p(\alpha)$ of optimal prices of the fairness-constrained problem $\max R_0(p_0)+R_1(p_1)$ s.t. $|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|M_0(b_0)-M_1(b_1)|$ with $p(0)=b$ exists on some $[0,\varepsilon]$, and for every such selection the welfare $\mathcal W(\alpha)=\sum_i R_i(p_i(\alpha))+d_iS_i(p_i(\alpha))$ has a finite right derivative $D$ at $0$ with $C(D)$.
--
--   Suppose $V_i\sim U(0,b_i)$ with $b_i>0$ and $0\le c<\min\{b_0,b_1\}$. Then a price pair is an unconstrained optimum if and only if
--   $$p_i^*=\frac{b_i+c}{2}\qquad(i=0,1),$$
--   and at this optimum (i) every $b_i>0$; (ii) near-optimal prices are localised: for every $\varepsilon>0$ there is $\delta>0$ with $R_i(p)\ge R_i(b_i)-\delta\Rightarrow|p-b_i|<\varepsilon$ for $p\ge0$; (iii) each $R_i$ is continuous near $b_i$; (iv) $R_i(b_i+h)=R_i(b_i)+\tfrac{r_i}{2}h^2+o(h^2)$; (v) $S_i'(b_i)=-\bar F_i(b_i)$, with curvature $r_i=-2d_i/b_i$; moreover $\bar F_i(p_i^*)=\dfrac{b_i-c}{2b_i}$.
--
--   These are the entries $p_i^*$, $R_i''(p_i^*)$ and $\bar F_i(p_i^*)$ of Table 3 (Online Appendix, p. 34; the printed $\bar F_i(p_i^*)$ omits the divisor $b_i$, see the mission insights) together with the regularity needed to apply the perturbation theorem.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; optimal prices under linear demand, §3, p. 8; Online Appendix, Table 3, p. 34.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

open Filter Topology Asymptotics

namespace CohenPriceFairness.LocalWelfare

theorem uniform_profit_regular (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 ≤ m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hcb : m.cost < min (bb 0) (bb 1))
    (hlaw : ∀ i, m.law i = uniformLaw (bb i)) :
    (∀ b : Prices, BaselineOptimal m b ↔ ∀ i, b i = (bb i + m.cost) / 2) ∧
    ∀ b : Prices, BaselineOptimal m b →
      (∀ i, 0 < b i) ∧
      (∀ ε > 0, ∃ δ > 0, ∀ i, ∀ p, 0 ≤ p → profit m i (b i) - δ ≤ profit m i p → |p - b i| < ε) ∧
      (∃ η > 0, ∀ i, ContinuousOn (profit m i) (Set.Icc (b i - η) (b i + η))) ∧
      (∀ i, (fun h => profit m i (b i + h) - profit m i (b i) - (-2 * m.population i / bb i) / 2 * h ^ 2)
        =o[𝓝 0] (fun h => h ^ 2)) ∧
      (∀ i, HasDerivAt (surplus m i) (-demand m i (b i)) (b i)) ∧
      (∀ i, demand m i (b i) = (bb i - m.cost) / (2 * bb i)) := by sorry

end CohenPriceFairness.LocalWelfare
