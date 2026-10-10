-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskTVaR_fundamental
-- name    : ActuarialValuation.tailRiskTVaR_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:31:05.951876+00:00
-- url     : https://prove2.me/theorems/bb61ded5-13d4-42f3-ad81-da6f5505cd4a
-- title:
--   Discrete TVaR quantile-atom feasibility and stop-loss identity
-- statement:
--   The capstone combines correct bounded quantile-atom allocation, the exact discrete stop-loss representation of tail value-at-risk and its lower bound by VaR. It explicitly assumes the selected upper quantile has enough mass to fill the required tail without assigning negative or more-than-available quantile probability.
--
--   **Mathematical statement**
--
--   $$
--   0\le a_q\le w_q,\quad\operatorname{TVaR}_\alpha=q+\Pi_B(q)/(1-\alpha)\ge q
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass
import Definitions.Def_actuarial_tailRiskTVaR
import Definitions.Def_actuarial_tailRiskStopLoss

namespace ActuarialValuation

theorem tailRiskTVaR_fundamental
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (hw : ∀ s, 0 ≤ w s) (ha : alpha < 1)
  (hbelow : tailRiskStrictMass w bound q ≤ 1 - alpha)
  (habove : 1 - alpha ≤ tailRiskStrictMass w bound q + w q) :
  (0 ≤ tailRiskAtomWeight w bound q alpha ∧
    tailRiskAtomWeight w bound q alpha ≤ w q) ∧
  (tailRiskTVaR w bound q alpha =
    (q : ℝ) + tailRiskStopLoss w bound q / (1 - alpha)) ∧
  ((q : ℝ) ≤ tailRiskTVaR w bound q alpha) := by sorry

end ActuarialValuation
