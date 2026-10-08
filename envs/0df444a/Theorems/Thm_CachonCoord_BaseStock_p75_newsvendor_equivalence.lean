-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_p75_newsvendor_equivalence
-- name    : CachonCoord.BaseStock.p75_newsvendor_equivalence
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:55:34.162009+00:00
-- url     : https://prove2.me/theorems/57b2feba-f0c4-46e9-8fa7-484ac41af85e
-- title:
--   §6.7.1, pp. 74–75 — with p = h_r + β_r and w = h_r the newsvendor profit is −c_r(q) + β_r μ_r
-- statement:
--   Let $D_r$ be the lead-time demand of the single-location base-stock model, with mean $\mu_r$, and use it as the demand of a newsvendor model in which the retailer's unit cost, goodwill costs and salvage value vanish ($c_r=g_r=g_s=v=0$). Write $S(q)=\mathbb E[\min(q,D_r)]$ for expected sales and $I(q)=\mathbb E[(q-D_r)^+]$ for expected leftover inventory, which coincides with the base-stock model's expected inventory $I_r(q)$. For a retail price $p$ and wholesale price $w$ the retailer's newsvendor profit is
--   $$\pi_r(q)=pS(q)-wq=(p-w)q-pI(q).$$
--   With $p=h_r+\beta_r$ and $w=h_r$,
--   $$\pi_r(q)=\beta_r q-(h_r+\beta_r)I_r(q)=-c_r(q)+\beta_r\mu_r,$$
--   where $c_r(q)=h_rI_r(q)+\beta_rB_r(q)$ is the retailer's base-stock cost. Hence a quantity $q$ maximizes $\pi_r$ if and only if it minimizes $c_r$.
--
--   This identity explains why coordination in the base-stock model mirrors coordination in the newsvendor model with buy-back contracts.
--
--   **Formalization Note** $S$ and $I$ are the published `SupplyChainTheory.expSales` and `SupplyChainTheory.expLeftover` applied to the lead-time demand law. The identities are stated for every real $q$, and maximization and minimization are over all real quantities.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, last paragraph of p. 74 and first displays of p. 75, pp. 74–75

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, pp. 74–75: the base-stock model is a newsvendor model.
With lead-time demand `D_r` as newsvendor demand and `c_r = g_r = g_s = v = 0`, the
newsvendor retailer's profit is `π_r(q) = pS(q) - wq = (p - w)q - pI(q)`, where
`S(q) = E[min(q, D_r)]` and `I(q) = E[(q - D_r)⁺]`. With `p = h_r + β_r` and `w = h_r`,
`π_r(q) = β_r q - (h_r + β_r)I_r(q) = -c_r(q) + β_r μ_r`, so maximizing `π_r` and
minimizing the base-stock cost `c_r` are the same problem. -/
theorem p75_newsvendor_equivalence (M : Model) :
    (∀ p w q : ℝ,
      p * SupplyChainTheory.expSales M.law q - w * q =
        (p - w) * q - p * SupplyChainTheory.expLeftover M.law q) ∧
    (∀ q : ℝ,
      (M.hr + M.br) * SupplyChainTheory.expSales M.law q - M.hr * q =
        M.br * q - (M.hr + M.br) * M.I q ∧
      M.br * q - (M.hr + M.br) * M.I q = -M.retailerCost q + M.br * M.meanDemand) ∧
    ∀ q : ℝ,
      IsMaxOn (fun x => (M.hr + M.br) * SupplyChainTheory.expSales M.law x - M.hr * x)
          Set.univ q ↔
        IsMinOn M.retailerCost Set.univ q := by sorry

end CachonCoord.BaseStock
