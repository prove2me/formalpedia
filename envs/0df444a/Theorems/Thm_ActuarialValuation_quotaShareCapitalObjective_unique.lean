-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareCapitalObjective_unique
-- name    : ActuarialValuation.quotaShareCapitalObjective_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:13:59.191393+00:00
-- url     : https://prove2.me/theorems/1374f861-0d12-46ea-9ff2-e1946df7b0cd
-- title:
--   Strict positive Bernoulli variance gives a unique optimiser
-- statement:
--   When claim probability is strictly between zero and one, claim amount nonzero and total variance coefficient strictly positive, the quadratic is strictly convex. Equality of any treaty cost to the optimum forces its retention to equal the unique candidate.
--
--   **Mathematical statement**
--
--   $$
--   J(r)=J(r^*)\Longrightarrow r=r^*
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Definitions.Def_actuarial_quotaShareContinuousOptimum

namespace ActuarialValuation

theorem quotaShareCapitalObjective_unique
  (q claim loading capital retention : ℝ)
  (hq0 : 0 < q) (hq1 : q < 1) (hb : claim ≠ 0)
  (hpos : 0 < loading + capital)
  (hEq : quotaShareCapitalObjective q claim retention loading capital =
     quotaShareCapitalObjective q claim
       (quotaShareContinuousOptimum loading capital) loading capital) :
  retention = quotaShareContinuousOptimum loading capital := by sorry

end ActuarialValuation
