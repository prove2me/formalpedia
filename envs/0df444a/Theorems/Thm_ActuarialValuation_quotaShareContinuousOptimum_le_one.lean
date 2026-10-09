-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareContinuousOptimum_le_one
-- name    : ActuarialValuation.quotaShareContinuousOptimum_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:10:27.385231+00:00
-- url     : https://prove2.me/theorems/b2b92b2b-7bc7-4837-890c-169fc4a8e808
-- title:
--   Nonnegative capital coefficient bounds optimal retention by one
-- statement:
--   The variance-premium loading is no greater than the sum of premium and capital coefficients. Division by their strictly positive sum yields an upper bound of one on the candidate retained quota fraction.
--
--   **Mathematical statement**
--
--   $$
--   r^*\le1
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareContinuousOptimum

namespace ActuarialValuation

theorem quotaShareContinuousOptimum_le_one (loading capital : ℝ)
  (hl : 0 ≤ loading) (hc : 0 ≤ capital)
  (hpos : 0 < loading + capital) :
  quotaShareContinuousOptimum loading capital ≤ 1 := by sorry

end ActuarialValuation
