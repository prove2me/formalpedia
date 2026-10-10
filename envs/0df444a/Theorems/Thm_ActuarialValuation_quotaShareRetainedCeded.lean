-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareRetainedCeded
-- name    : ActuarialValuation.quotaShareRetainedCeded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:01:42.44351+00:00
-- url     : https://prove2.me/theorems/e04ccb30-e208-4a70-bb7a-2b4910923265
-- title:
--   Quota-share conservation of the original claim
-- statement:
--   Adding the direct insurer's payment and the reinsurer's payment for the same realised claim reproduces the original insured amount. This pointwise partition is independent of the frequency distribution or cost-loading principle.
--
--   **Mathematical statement**
--
--   $$
--   R_r(X)+C_r(X)=X
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareRetainedClaim
import Definitions.Def_actuarial_quotaShareCededClaim

namespace ActuarialValuation

theorem quotaShareRetainedCeded (claim retention : ℝ) :
  quotaShareRetainedClaim claim retention +
    quotaShareCededClaim claim retention = claim := by sorry

end ActuarialValuation
