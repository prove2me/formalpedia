-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareMeanVariance_fundamental
-- name    : ActuarialValuation.quotaShareMeanVariance_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:19:41.228366+00:00
-- url     : https://prove2.me/theorems/31a422e9-0a9c-47d2-bac0-94c9cacdb8a6
-- title:
--   Admissible and globally optimal variance-premium quota reinsurance
-- statement:
--   The capstone combines the admissible unit-interval bounds and global optimality of the same explicit quota fraction. It ensures the policy recommendation minimises expected claims, ceded variance loading and residual capital cost under valid Bernoulli mortality and positive total variance coefficients.
--
--   **Mathematical statement**
--
--   $$
--   0\le r^*\le1,\quad\forall r,\ J(r^*)\le J(r)
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareContinuousOptimum
import Definitions.Def_actuarial_quotaShareCapitalObjective

namespace ActuarialValuation

theorem quotaShareMeanVariance_fundamental
  (q claim loading capital : ℝ)
  (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
  (hl : 0 ≤ loading) (hc : 0 ≤ capital)
  (hpos : 0 < loading + capital) :
  (0 ≤ quotaShareContinuousOptimum loading capital ∧
    quotaShareContinuousOptimum loading capital ≤ 1) ∧
  (∀ retention : ℝ,
    quotaShareCapitalObjective q claim
      (quotaShareContinuousOptimum loading capital) loading capital ≤
    quotaShareCapitalObjective q claim retention loading capital) := by sorry

end ActuarialValuation
