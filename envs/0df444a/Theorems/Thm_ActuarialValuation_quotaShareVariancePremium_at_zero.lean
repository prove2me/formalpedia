-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareVariancePremium_at_zero
-- name    : ActuarialValuation.quotaShareVariancePremium_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:03:37.994757+00:00
-- url     : https://prove2.me/theorems/3c642d33-bb71-4f65-ae05-4a05c360720a
-- title:
--   Full cession produces the entire loaded claim premium
-- statement:
--   At zero retention, the insurer cedes all claim amounts. For a fixed claim payable with Bernoulli probability q, the reinsurer charges the claim expectation plus a multiple of its full original variance.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_0=qb+\lambda q(1-q)b^2
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareVariancePremium

namespace ActuarialValuation

theorem quotaShareVariancePremium_at_zero (q claim loading : ℝ) :
  quotaShareVariancePremium q claim 0 loading =
    q * claim + loading * q * (1 - q) * claim ^ 2 := by sorry

end ActuarialValuation
