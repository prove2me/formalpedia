-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareVariancePremium_at_full
-- name    : ActuarialValuation.quotaShareVariancePremium_at_full
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:03:10.677774+00:00
-- url     : https://prove2.me/theorems/90e43970-0605-422f-81ce-3cc87e073704
-- title:
--   Full retention produces no ceded premium
-- statement:
--   If the insurer retains one hundred per cent of the claim there is no ceded payment at all, so both the reinsurer's expected loss and the variance loading disappear from the premium calculation.
--
--   **Mathematical statement**
--
--   $$
--   \Pi_1=0
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareVariancePremium

namespace ActuarialValuation

theorem quotaShareVariancePremium_at_full (q claim loading : ℝ) :
  quotaShareVariancePremium q claim 1 loading = 0 := by sorry

end ActuarialValuation
