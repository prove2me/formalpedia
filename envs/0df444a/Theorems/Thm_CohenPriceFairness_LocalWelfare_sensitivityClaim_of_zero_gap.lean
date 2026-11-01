-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_sensitivityClaim_of_zero_gap
-- name    : CohenPriceFairness.LocalWelfare.sensitivityClaim_of_zero_gap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:25.234509+00:00
-- url     : https://prove2.me/theorems/bead3800-1830-4a3c-9e46-d95e39705a8f
-- title:
--   Sensitivity claim when the baseline fairness gap is zero
-- statement:
--   Throughout, a market has two groups $i\in\{0,1\}$ with masses $d_i>0$, cost $c\ge0$ and valuation laws $\mu_i$; $\bar F_i(p)=\mu_i([p,\infty))$ is the purchase probability, $R_i(p)=d_i(p-c)\bar F_i(p)$ the profit, $S_i(p)=\int(v-p)^+\,d\mu_i$ the surplus and $N_i(p)$ the mean valuation of non-buyers. For a fairness measure $M_i\in\{p,\bar F_i,S_i,N_i\}$, a *sensitivity claim* $\mathrm{SC}(b,M,C)$ at baseline prices $b$ says: a selection $\alpha\mapsto p(\alpha)$ of optimal prices of the fairness-constrained problem $\max R_0(p_0)+R_1(p_1)$ s.t. $|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|M_0(b_0)-M_1(b_1)|$ with $p(0)=b$ exists on some $[0,\varepsilon]$, and for every such selection the welfare $\mathcal W(\alpha)=\sum_i R_i(p_i(\alpha))+d_iS_i(p_i(\alpha))$ has a finite right derivative $D$ at $0$ with $C(D)$.
--
--   Suppose $b$ is the unique baseline optimum (every pair of unconstrained optimal prices equals $b$) and the baseline fairness gap vanishes, $M_0(b_0)=M_1(b_1)$. Then for every condition $C$ with $C(0)$, the sensitivity claim $\mathrm{SC}(b,M,C)$ holds, with right derivative $\mathcal W'(0)=0$.
--
--   This covers the degenerate case in Theorem 2 where a fairness constraint does not bind, e.g. demand fairness at zero cost.
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; Problem (1), p. 4; degenerate case of Theorem 2, p. 7.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity

namespace CohenPriceFairness.LocalWelfare

theorem sensitivityClaim_of_zero_gap (m : Market) (b : Prices) (k : Metric) (C : ℝ → Prop)
    (hC : C 0) (hb : BaselineOptimal m b) (huniq : ∀ b' : Prices, BaselineOptimal m b' → b' = b)
    (hgap : metricValue m k 0 (b 0) = metricValue m k 1 (b 1)) :
    SensitivityClaim m b k C := by sorry

end CohenPriceFairness.LocalWelfare
