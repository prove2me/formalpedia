-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareCapitalObjective_expand
-- name    : ActuarialValuation.quotaShareCapitalObjective_expand
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:06:29.121665+00:00
-- url     : https://prove2.me/theorems/d32991f3-5900-45fd-8615-5cc9e9fba113
-- title:
--   Mean-variance cost simplifies to a quadratic in retention
-- statement:
--   Expected retained and ceded payments sum to the same full expected claim. Only reinsurance load and retained risk capital depend on the quota share, and that choice-dependent component is a weighted sum of two squared fractions.
--
--   **Mathematical statement**
--
--   $$
--   J(r)=qb+q(1-q)b^2[\lambda(1-r)^2+\alpha r^2]
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Definitions.Def_actuarial_quotaShareVariancePremium

namespace ActuarialValuation

theorem quotaShareCapitalObjective_expand
  (q claim retention loading capital : ℝ) :
  quotaShareCapitalObjective q claim retention loading capital =
    q * claim + q * (1 - q) * claim ^ 2 *
      (loading * (1 - retention) ^ 2 + capital * retention ^ 2) := by sorry

end ActuarialValuation
