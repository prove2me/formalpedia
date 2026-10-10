-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareCapitalObjective_optimal
-- name    : ActuarialValuation.quotaShareCapitalObjective_optimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:13:10.04299+00:00
-- url     : https://prove2.me/theorems/631234b8-17fd-42ed-a366-9a5cf144a3a4
-- title:
--   The continuous quota-share solution minimises total insurer cost
-- statement:
--   The completed square is nonnegative under a genuine Bernoulli probability, nonnegative claim variance and positive total cost load. It vanishes at the proposed quota share, establishing global mean-variance optimality over real fractions and hence over admissible contracts.
--
--   **Mathematical statement**
--
--   $$
--   J(r^*)\le J(r)\text{ for every real }r
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareCapitalObjective
import Definitions.Def_actuarial_quotaShareContinuousOptimum

namespace ActuarialValuation

theorem quotaShareCapitalObjective_optimal
  (q claim loading capital retention : ℝ)
  (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
  (hl : 0 ≤ loading) (hc : 0 ≤ capital)
  (hpos : 0 < loading + capital) :
  quotaShareCapitalObjective q claim
       (quotaShareContinuousOptimum loading capital) loading capital ≤
    quotaShareCapitalObjective q claim retention loading capital := by sorry

end ActuarialValuation
