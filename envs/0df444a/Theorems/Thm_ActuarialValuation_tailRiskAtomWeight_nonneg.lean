-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskAtomWeight_nonneg
-- name    : ActuarialValuation.tailRiskAtomWeight_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:59:14.040586+00:00
-- url     : https://prove2.me/theorems/048a3a48-b2c4-4d26-94c4-ce064744148a
-- title:
--   A valid upper-quantile tail has nonnegative selected atom mass
-- statement:
--   Once the mass strictly beyond q is no larger than the required tail probability, the remaining probability to be assigned from the quantile atom is nonnegative. This direction of the inequality is essential when the discrete VaR boundary splits an atom.
--
--   **Mathematical statement**
--
--   $$
--   T_B(q)\le1-\alpha\Rightarrow a_q\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskAtomWeight
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

theorem tailRiskAtomWeight_nonneg
  (w : ℕ → ℝ) (bound q : ℕ) (alpha : ℝ)
  (htail : tailRiskStrictMass w bound q ≤ 1 - alpha) :
  0 ≤ tailRiskAtomWeight w bound q alpha := by sorry

end ActuarialValuation
