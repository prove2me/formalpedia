-- Prove2me | Theorems.Thm_ActuarialValuation_quotaShareQuadratic_square_completion
-- name    : ActuarialValuation.quotaShareQuadratic_square_completion
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:12:01.856751+00:00
-- url     : https://prove2.me/theorems/0b818a90-aafc-4d14-be1d-407ac554c434
-- title:
--   Complete the square around the optimal quota fraction
-- statement:
--   The premium and capital quadratic is a fixed base cost plus total coefficient times the square of the deviation from the candidate optimal retention. The identity is algebraic and requires the denominator to be nonzero, while nonnegative total coefficient is needed to deduce minimality.
--
--   **Mathematical statement**
--
--   $$
--   \lambda(1-r)^2+\alpha r^2=\frac{\lambda\alpha}{\lambda+\alpha}+(\lambda+\alpha)(r-r^*)^2
--   $$
-- source:
--   Kaluszka (2001), Optimal reinsurance under mean-variance premium principles, DOI https://doi.org/10.1016/S0167-6687(00)00066-4; Guerra and Centeno (2010), ASTIN Bulletin 40, DOI https://doi.org/10.2143/AST.40.1.2049220; explicit Bernoulli quota-share specialisation

import Mathlib
import Definitions.Def_actuarial_quotaShareContinuousOptimum

namespace ActuarialValuation

theorem quotaShareQuadratic_square_completion
  (loading capital retention : ℝ)
  (hpos : loading + capital ≠ 0) :
  loading * (1 - retention) ^ 2 + capital * retention ^ 2 =
    (loading * capital / (loading + capital)) +
      (loading + capital) *
        (retention - quotaShareContinuousOptimum loading capital) ^ 2 := by sorry

end ActuarialValuation
