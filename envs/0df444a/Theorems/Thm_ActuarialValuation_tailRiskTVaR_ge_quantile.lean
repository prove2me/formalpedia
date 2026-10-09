-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskTVaR_ge_quantile
-- name    : ActuarialValuation.tailRiskTVaR_ge_quantile
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:26:22.481855+00:00
-- url     : https://prove2.me/theorems/5fa3909b-30e8-44c1-9ece-5c4364cdd9b5
-- title:
--   Tail value-at-risk is no smaller than the loss quantile
-- statement:
--   Expected excess above the quantile is nonnegative under genuine nonnegative masses. Since one minus confidence is positive, the TVaR stop-loss representation implies that the average of the worst tail outcomes cannot fall below its baseline quantile.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{TVaR}_\alpha\ge q
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskStopLoss

namespace ActuarialValuation

theorem tailRiskTVaR_ge_quantile
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (hw : ∀ s, 0 ≤ w s) (ha : alpha < 1) :
  (q : ℝ) ≤ tailRiskTVaR w bound q alpha := by sorry

end ActuarialValuation
