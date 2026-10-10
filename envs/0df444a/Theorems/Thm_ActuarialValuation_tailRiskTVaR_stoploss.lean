-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskTVaR_stoploss
-- name    : ActuarialValuation.tailRiskTVaR_stoploss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:25:40.301896+00:00
-- url     : https://prove2.me/theorems/4239c7fa-10ad-499a-b956-4846ed0b62a7
-- title:
--   Tail value-at-risk has the stop-loss representation
-- statement:
--   At a confidence strictly less than one, dividing the tail monetary numerator by positive tail probability gives TVaR as VaR q plus the expected excess over q divided by one-minus-alpha. This is the correct formula even when there is substantial loss probability at q.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{TVaR}_\alpha=q+\Pi_B(q)/(1-\alpha)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskSelectedLoss
import Definitions.Def_actuarial_tailRiskStopLoss

namespace ActuarialValuation

theorem tailRiskTVaR_stoploss
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (ha : alpha < 1) :
  tailRiskTVaR w bound q alpha =
    (q : ℝ) + tailRiskStopLoss w bound q / (1 - alpha) := by sorry

end ActuarialValuation
