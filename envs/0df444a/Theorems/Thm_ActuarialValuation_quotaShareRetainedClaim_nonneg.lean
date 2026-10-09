-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareRetainedClaim_nonneg
-- name    : ActuarialValuation.quotaShareRetainedClaim_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:02:37.979472+00:00
-- url     : https://prove2.me/theorems/0e3c6ed2-b27d-4f66-b768-d2b2057055e7
-- title:
--   Nonnegative retention implies nonnegative insurer claim
-- statement:
--   The retained loss is the product of the policyholder claim and the retained quota percentage. Nonnegative inputs make the insurer's claim nonnegative, including the zero-retention contract.
--
--   **Mathematical statement**
--
--   $$
--   b,r\ge0\Longrightarrow R_r(b)\ge0
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareRetainedClaim

namespace ActuarialValuation

theorem quotaShareRetainedClaim_nonneg (claim retention : ℝ)
  (hb : 0 ≤ claim) (hr : 0 ≤ retention) :
  0 ≤ quotaShareRetainedClaim claim retention := by sorry

end ActuarialValuation
