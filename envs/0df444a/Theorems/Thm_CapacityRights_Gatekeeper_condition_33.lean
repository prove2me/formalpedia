-- Prove2me | Theorems.Thm_CapacityRights_Gatekeeper_condition_33
-- name    : CapacityRights.Gatekeeper.condition_33
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:39:02.158993+00:00
-- url     : https://prove2.me/theorems/c8afa05c-e80e-44c8-9fe1-dd1eb6611c71
-- title:
--   Equation (33): upstream best-response marginal condition
-- statement:
--   Fix a nonnegative capacity right $k_2$ for Division 2, a fixed transfer $p$, and a period $t$ under the annuity depreciation rule. If Division 1's chosen own capacity $k_1\ge0$ maximizes its expected residual income, then
--
--   $$
--   (1-\delta)\mathbb E[CM'_1(k_1\mid w_1,\tilde\epsilon_1)]
--   +\delta\mathbb E[S(k_1+k_2\mid w,\tilde\epsilon)]\le c.
--   $$
--
--   Equality holds whenever $k_1>0$. This is the marginal incentive condition for an upstream best response to a gatekeeper contract.
--
--   **Formalization Note** At $k_1=0$, the marginal values are right derivatives on nonnegative capacity. The fixed payment shifts residual income but does not change the best response.
-- source:
--   Dutta & Reichelstein, Capacity Rights and Full Cost Transfer Pricing, CESifo Working Paper No. 7968 (November 2019), p. 43 (PDF 46), proof of Proposition 3, equation (33)

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

namespace CapacityRights.Gatekeeper

open MeasureTheory

/-- Equation (33) in the proof of Proposition 3, p. 43 (PDF 46). -/
theorem condition_33 (E : Env) (hS : E.Standing)
    (d : ℕ → ℝ) (hd : IsAnnuity E d)
    (t : ℕ) (ht : t ∈ Finset.Icc 1 E.T)
    (k2 p k1 : ℝ) (hk2 : 0 ≤ k2)
    (hbr : IsBestResponse1 E d t k2 p k1) :
    (1 - E.δ) * (∫ e, marginal1 E k1 e.1 ∂E.μ) +
      E.δ * (∫ e, S E (k1 + k2) e ∂E.μ) ≤ ucc E ∧
    (0 < k1 →
      (1 - E.δ) * (∫ e, marginal1 E k1 e.1 ∂E.μ) +
        E.δ * (∫ e, S E (k1 + k2) e ∂E.μ) = ucc E) := by sorry

end CapacityRights.Gatekeeper
