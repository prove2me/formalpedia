-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_eq_33
-- name    : CachonCoord.BaseStock.eq_33
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:54:16.043079+00:00
-- url     : https://prove2.me/theorems/7b809381-8325-4a75-8c8f-27a4408c9c4b
-- title:
--   Eq. (33), p. 74 — the transfer coordinates the base-stock level and splits channel costs
-- statement:
--   In the single-location base-stock model, let $c=c_r+c_s$ be channel cost and let $s_r^\circ>0$ be its unique cost-minimizing stock level, characterized by $F_r(s_r^\circ)=\beta/(h_r+\beta)$. For every $0<\lambda\le1$, choose the supplier-to-retailer transfer rates $t_I=(1-\lambda)h_r$ and $t_B=\beta_r-\lambda\beta$. At every real stock level $s$,
--   $$c_r^\lambda(s)=\lambda c(s),\qquad c_s^\lambda(s)=(1-\lambda)c(s).$$
--   Consequently, $s_r^\circ$ is the unique minimizer of the retailer's contracted cost as well as of the channel cost. The contract coordinates the supply chain and assigns the fraction $\lambda$ of its cost to the retailer; at every stock level $s$ the retailer's contracted cost $c_r^\lambda(s)$ is strictly increasing in $\lambda\in(0,1]$, so the retailer's share of the cost increases with $\lambda$.
--
--   This is the section's coordinating-contract result: the firms' cost objectives are aligned at the integrated optimum.
--
--   **Formalization Note** The contracted costs are defined by subtracting or adding the printed transfer $t_I I_r+t_B B_r$ from the original costs, so the identity is a substantive claim. The interval $(0,1]$ excludes $\lambda=0$, at which every stock level would minimize the retailer's cost. Optimization is over all real levels; the common optimum is positive. Risk neutrality and full information are standing chapter assumptions. The long-run average cost reduction asserted on p. 73 is represented by its displayed cost functions.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eq. (33) and following paragraph, p. 74

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (33) and following paragraph, p. 74:
the printed transfers split channel costs and make its unique optimum the
retailer's unique optimum for every `λ ∈ (0,1]`; the retailer's contracted cost at
each stock level is strictly increasing in `λ` ("the retailer's share of the cost increasing in
the parameter λ"). -/
theorem eq_33 (M : Model) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      (∀ s : ℝ, M.contractedRetailerCost lam s = lam * M.chainCost s ∧
        M.contractedSupplierCost lam s = (1 - lam) * M.chainCost s) ∧
      (∀ s : ℝ, StrictMonoOn (fun l => M.contractedRetailerCost l s) (Set.Ioc 0 1)) ∧
      ∃ so : ℝ, 0 < so ∧ M.F so = M.beta / (M.hr + M.beta) ∧
        IsMinOn M.chainCost Set.univ so ∧
        IsMinOn (M.contractedRetailerCost lam) Set.univ so ∧
        (∀ s : ℝ, IsMinOn M.chainCost Set.univ s → s = so) ∧
        (∀ s : ℝ, IsMinOn (M.contractedRetailerCost lam) Set.univ s → s = so) := by sorry

end CachonCoord.BaseStock
