-- Prove2me | Theorems.Thm_CohenPriceFairness_LocalWelfare_uniform_demand_claim
-- name    : CohenPriceFairness.LocalWelfare.uniform_demand_claim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-01T02:13:27.676955+00:00
-- url     : https://prove2.me/theorems/90579e83-d250-4be4-a355-40a95e774b07
-- title:
--   Theorem 2, uniform valuations: $W'(0)<0$ under demand fairness
-- statement:
--   Throughout, a market has two groups $i\in\{0,1\}$ with masses $d_i>0$, cost $c\ge0$ and valuation laws $\mu_i$; $\bar F_i(p)=\mu_i([p,\infty))$ is the purchase probability, $R_i(p)=d_i(p-c)\bar F_i(p)$ the profit, $S_i(p)=\int(v-p)^+\,d\mu_i$ the surplus and $N_i(p)$ the mean valuation of non-buyers. For a fairness measure $M_i\in\{p,\bar F_i,S_i,N_i\}$, a *sensitivity claim* $\mathrm{SC}(b,M,C)$ at baseline prices $b$ says: a selection $\alpha\mapsto p(\alpha)$ of optimal prices of the fairness-constrained problem $\max R_0(p_0)+R_1(p_1)$ s.t. $|M_0(p_0)-M_1(p_1)|\le(1-\alpha)|M_0(b_0)-M_1(b_1)|$ with $p(0)=b$ exists on some $[0,\varepsilon]$, and for every such selection the welfare $\mathcal W(\alpha)=\sum_i R_i(p_i(\alpha))+d_iS_i(p_i(\alpha))$ has a finite right derivative $D$ at $0$ with $C(D)$.
--
--   Suppose $V_i\sim U(0,b_i)$ with $b_i>0$, $b_0\ne b_1$ and $0<c<\min\{b_0,b_1\}$. Then for every pair $b$ of unconstrained optimal prices, the sensitivity claim holds under demand fairness with
--   $$
--   \mathcal W'(0)<0.
--   $$
--
--   This is the demand fairness case of Theorem 2 (p. 7) for uniform valuations. The assumption $c>0$ is needed: at $c=0$ both groups have the same purchase probability at their optimal prices, so the constraint does not bind and $\mathcal W'(0)=0$. It is one of the building blocks of the proof of Theorem 2 (p. 7; proof in Online Appendix A, p. 33).
-- source:
--   Cohen, Elmachtoub and Lei, Price Discrimination with Fairness Constraints, Management Science (2022), https://doi.org/10.1287/mnsc.2022.4317; page numbers refer to the published article and its Online Appendix; Theorem 2, p. 7 (demand fairness, uniform valuations); proof in Online Appendix A, p. 33, with Table 3, p. 34.

import Mathlib
import Definitions.Def_CohenPriceFairness_LocalWelfare_Sensitivity
import Definitions.Def_CohenPriceFairness_LocalWelfare_Families

namespace CohenPriceFairness.LocalWelfare

theorem uniform_demand_claim (m : Market) (hd : ∀ i, 0 < m.population i) (hc : 0 < m.cost)
    (bb : Fin 2 → ℝ) (hbb : ∀ i, 0 < bb i) (hne : bb 0 ≠ bb 1)
    (hcb : m.cost < min (bb 0) (bb 1)) (hlaw : ∀ i, m.law i = uniformLaw (bb i))
    (b : Prices) (hb : BaselineOptimal m b) :
    SensitivityClaim m b .demand (fun D => D < 0) := by sorry

end CohenPriceFairness.LocalWelfare
