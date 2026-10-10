-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskStopLoss_above
-- name    : ActuarialValuation.tailRiskStopLoss_above
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:56:04.012252+00:00
-- url     : https://prove2.me/theorems/102d89a5-b84f-4484-bf3d-918cfe86e615
-- title:
--   Excess loss vanishes when quantile is above maximum
-- statement:
--   A quantile at or above the largest supported loss makes every realised excess payout zero. This is the exact terminal stop-loss boundary condition, including a quantile greater than the maximum.
--
--   **Mathematical statement**
--
--   $$
--   q\ge B\Rightarrow \Pi_B(q)=0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskStopLoss

namespace ActuarialValuation

theorem tailRiskStopLoss_above (w : ℕ → ℝ) (bound q : ℕ)
  (h : bound ≤ q) : tailRiskStopLoss w bound q = 0 := by sorry

end ActuarialValuation
