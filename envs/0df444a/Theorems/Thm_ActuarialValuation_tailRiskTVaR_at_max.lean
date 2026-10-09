-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskTVaR_at_max
-- name    : ActuarialValuation.tailRiskTVaR_at_max
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:27:35.362391+00:00
-- url     : https://prove2.me/theorems/b28015e9-abaa-4c85-b35e-29b2697cbea5
-- title:
--   At the maximum supported quantile, tail value-at-risk equals that maximum
-- statement:
--   When the quantile is the maximum possible aggregate loss, every strict excess payout is zero. The worst-tail numerator then contains only a fraction of probability mass valued at that maximum, so its conditional average equals the maximum itself.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{TVaR}_\alpha(q=B)=B
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskStopLoss

namespace ActuarialValuation

theorem tailRiskTVaR_at_max
  (w : ℕ → ℝ) (bound : ℕ) (alpha : ℝ) (ha : alpha < 1) :
  tailRiskTVaR w bound bound alpha = (bound : ℝ) := by sorry

end ActuarialValuation
