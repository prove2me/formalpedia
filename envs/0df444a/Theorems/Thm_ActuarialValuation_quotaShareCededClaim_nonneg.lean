-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareCededClaim_nonneg
-- name    : ActuarialValuation.quotaShareCededClaim_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:02:10.577555+00:00
-- url     : https://prove2.me/theorems/83dee686-9205-4c7e-a727-8e6a65fb0294
-- title:
--   Admissible fraction gives nonnegative ceded claim
-- statement:
--   A nonnegative insured loss multiplied by the nonnegative complementary quota fraction is a nonnegative ceded loss. The restriction to a fraction between zero and one prevents the treaty from transferring a negative claim to the reinsurer.
--
--   **Mathematical statement**
--
--   $$
--   b\ge0,\ 0\le r\le1\Longrightarrow C_r(b)\ge0
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareCededClaim

namespace ActuarialValuation

theorem quotaShareCededClaim_nonneg (claim retention : ℝ)
  (hb : 0 ≤ claim) (hr0 : 0 ≤ retention) (hr1 : retention ≤ 1) :
  0 ≤ quotaShareCededClaim claim retention := by sorry

end ActuarialValuation
