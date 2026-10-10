-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareContinuousOptimum_nonneg
-- name    : ActuarialValuation.quotaShareContinuousOptimum_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:07:01.032718+00:00
-- url     : https://prove2.me/theorems/57c99499-e93d-4217-84d1-90f97ad80735
-- title:
--   Nonnegative loadings give nonnegative optimal retention
-- statement:
--   Positive total loading and a nonnegative numerator make the closed-form candidate at least zero, including the boundary when the ceded-variance premium has no positive variance loading.
--
--   **Mathematical statement**
--
--   $$
--   r^*\ge0
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareContinuousOptimum

namespace ActuarialValuation

theorem quotaShareContinuousOptimum_nonneg (loading capital : ℝ)
  (hl : 0 ≤ loading) (hc : 0 ≤ capital)
  (hpos : 0 < loading + capital) :
  0 ≤ quotaShareContinuousOptimum loading capital := by sorry

end ActuarialValuation
