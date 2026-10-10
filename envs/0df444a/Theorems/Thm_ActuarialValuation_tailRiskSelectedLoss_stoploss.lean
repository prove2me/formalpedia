-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskSelectedLoss_stoploss
-- name    : ActuarialValuation.tailRiskSelectedLoss_stoploss
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:24:23.103854+00:00
-- url     : https://prove2.me/theorems/4656091a-5dbc-47ed-aa5b-f5f21130c18c
-- title:
--   Tie-adjusted tail numerator equals quantile mass plus stop-loss excess
-- statement:
--   Every amount above quantile q contributes the quantile itself plus its excess, while selected quantile-level outcomes contribute q without excess. Summing finite payments and simplifying the selected probability fraction yields the quantile-times-tail-mass plus expected stop-loss premium.
--
--   **Mathematical statement**
--
--   $$
--   A_B(q,\alpha)=q(1-\alpha)+\Pi_B(q)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskSelectedLoss
import Definitions.Def_actuarial_tailRiskStopLoss
import Definitions.Def_actuarial_tailRiskStrictMass
import Definitions.Def_actuarial_tailRiskAtomWeight

namespace ActuarialValuation

theorem tailRiskSelectedLoss_stoploss
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) :
  tailRiskSelectedLoss w bound q alpha =
    (q : ℝ) * (1 - alpha) + tailRiskStopLoss w bound q := by sorry

end ActuarialValuation
