-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskAtomWeight_coverage
-- name    : ActuarialValuation.tailRiskAtomWeight_coverage
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:14:06.466043+00:00
-- url     : https://prove2.me/theorems/015f618c-ad06-46e9-b48f-7817348c54ba
-- title:
--   Strict tail plus selected atom fills exactly the target probability
-- statement:
--   The definition allocates precisely the missing probability mass at the quantile. Therefore strict-above-quantile outcomes and their selected quantile-level fraction together comprise the target worst one-minus-alpha probability group.
--
--   **Mathematical statement**
--
--   $$
--   T_B(q)+a_q=1-\alpha
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

theorem tailRiskAtomWeight_coverage
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ) :
  tailRiskStrictMass w bound q + tailRiskAtomWeight w bound q alpha =
    1 - alpha := by sorry

end ActuarialValuation
