-- Prove2me | Theorems.Thm_CachonCoord_BaseStock_eq_32
-- name    : CachonCoord.BaseStock.eq_32
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:53:26.542748+00:00
-- url     : https://prove2.me/theorems/61bc6dc8-b1f0-4d21-8b8b-699dc257e3f4
-- title:
--   Eq. (32), p. 74 — contracted retailer cost and positive coefficients
-- statement:
--   For $0<\lambda\le1$, set $t_I=(1-\lambda)h_r$ and $t_B=\beta_r-\lambda\beta$, where $\beta=\beta_r+\beta_s$. The supplier pays $t_I I_r(s)+t_B B_r(s)$ to the retailer, so for every real $s$ the retailer's cost becomes
--   $$c_r^\lambda(s)=(\beta_r-t_B)(\mu_r-s)+(h_r+\beta_r-t_I-t_B)I_r(s).$$
--   Moreover, $\beta_r-t_B=\lambda\beta>0$ and $h_r+\beta_r-t_I-t_B=\lambda(h_r+\beta)>0$.
--
--   These coefficients prepare the comparison between the contracted retailer cost and the channel cost in (33).
--
--   **Formalization Note** The transfer is positive from supplier to retailer, as specified on p. 73. The retailer's contracted cost is defined as original cost minus that transfer, independently of the target identity.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.7.1, Eq. (32) and the two following displays, p. 74

import Mathlib
import Definitions.Def_CachonCoord_BaseStock_Model

open MeasureTheory ProbabilityTheory

namespace CachonCoord.BaseStock

/-- Cachon (2003), §6.7.1, Eq. (32) and the two parameter identities,
p. 74: the retailer's cost after the supplier-to-retailer transfer. -/
theorem eq_32 (M : Model) :
    ∀ lam : ℝ, 0 < lam → lam ≤ 1 →
      (∀ s : ℝ, M.contractedRetailerCost lam s =
        (M.br - M.tB lam) * (M.meanDemand - s) +
          (M.hr + M.br - M.tI lam - M.tB lam) * M.I s) ∧
      M.br - M.tB lam = lam * M.beta ∧
      0 < M.br - M.tB lam ∧
      M.hr + M.br - M.tI lam - M.tB lam = lam * (M.hr + M.beta) ∧
      0 < M.hr + M.br - M.tI lam - M.tB lam := by sorry

end CachonCoord.BaseStock
