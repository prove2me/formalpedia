-- Prove2me | Theorems.Thm_CachonPushPull_Coordination_apd_pareto_coordinates
-- name    : CachonPushPull.Coordination.apd_pareto_coordinates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T19:35:22.795603+00:00
-- url     : https://prove2.me/theorems/95b881fd-337b-404f-86e7-b4f52891b550
-- title:
--   Theorem 7 — advance-purchase discounts with $w_2 = p$ are Pareto, the Pareto set coordinates the chain, and any division of $\Pi^o$ is achievable
-- statement:
--   Let demand satisfy the standing assumptions ($F(0) = 0$, $F$ strictly increasing on $[0,\infty)$ with a density on $(0,\infty)$, IGFR), let $v < c < p$, and let $q^o$ satisfy $F(q^o) = (p - c)/(p - v)$, with $\Pi^o = \Pi(q^o)$ the supply chain's optimal expected profit. Contracts are pairs $\{w_1, w_2\}$ of wholesale prices, compared among the push, pull and advance-purchase discount contracts; outcomes of a contract are the prebook–production pairs $(y, q)$ in which the supplier best-responds to the prebook and the retailer prebooks optimally anticipating that response. Then:
--
--   1. every advance-purchase discount contract with $w_2 = p$ and $c \le w_1 \le w_2$ has an outcome and is Pareto;
--   2. every outcome $(y, q)$ of every Pareto contract has efficiency $100\%$:
--   $$
--   \Pi(q) = \Pi^o ;
--   $$
--   3. any division of the supply chain's profit is achievable: for every $r \in [0, \Pi^o]$ there are $w_1 \in [c, p]$ and an outcome $(y, q)$ of $\{w_1, p\}$ with $\pi_r(y, q) = r$ and $\pi_s(y, q) = \Pi^o - r$.
--
--   The theorem shows that supply chain coordination with an arbitrary allocation of profit is achievable with wholesale-price contracts alone: the at-once price $w_2 = p$ gives the supplier the chain's marginal incentive for capacity, and the prebook discount $w_1$ moves profit between the firms without distorting either firm's decision.
--
--   **Formalization Note** "Includes all" is read as membership of every such contract in the Pareto set, and each of its outcomes must be undominated. The efficiency sentence ranges over every Pareto contract, not only the $w_2 = p$ family. "Any division is achievable" is read as surjectivity of the payoff split onto $[0, \Pi^o]$. The contract classes carry the lower bound $w_1 \ge c$ (see the Game definition). The theorem does not use the IGFR assumption; it is kept so the series shares one demand model.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 233, Section 4.5, Theorem 7

import Mathlib
import Definitions.Def_CachonPushPull_Coordination_Game

namespace CachonPushPull.Coordination

open MeasureTheory ProbabilityTheory

/-- Theorem 7, p. 233. Among the push, pull and advance-purchase discount contracts:
1. every contract `{w₁, p}` with `c ≤ w₁ ≤ p` has an outcome and is Pareto;
2. every outcome `(y, q)` of every Pareto contract is efficient: `Π(q) = Π^o = Π(q^o)`;
3. any division of `Π^o` is achievable: for every `r ∈ [0, Π^o]` some contract `{w₁, p}` with
   `c ≤ w₁ ≤ p` has an outcome giving the retailer `r` and the supplier `Π^o - r`. -/
theorem apd_pareto_coordinates (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (qo : ℝ) (hqo : cdf μ qo = (p - c) / (p - v)) :
    (∀ w₁ : ℝ, c ≤ w₁ → w₁ ≤ p →
      (∃ y q : ℝ, IsOutcome μ p c v w₁ p y q) ∧ IsPareto μ p c v w₁ p) ∧
    (∀ w₁ w₂ : ℝ, IsPareto μ p c v w₁ w₂ →
      ∀ y q : ℝ, IsOutcome μ p c v w₁ w₂ y q →
        chainProfit μ p c v q = chainProfit μ p c v qo) ∧
    ∀ r : ℝ, 0 ≤ r → r ≤ chainProfit μ p c v qo →
      ∃ w₁ : ℝ, c ≤ w₁ ∧ w₁ ≤ p ∧ ∃ y q : ℝ, IsOutcome μ p c v w₁ p y q ∧
        retailerProfit μ p v w₁ p y q = r ∧
        supplierProfit μ p c v w₁ p y q = chainProfit μ p c v qo - r := by sorry

end CachonPushPull.Coordination
