-- Prove2me | Theorems.Thm_ActuarialValuation_tailRiskStrictMass_nonneg
-- name    : ActuarialValuation.tailRiskStrictMass_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:54:21.097819+00:00
-- url     : https://prove2.me/theorems/f465ca1a-879e-430e-a69e-f539968c962b
-- title:
--   Nonnegative claim weights yield a nonnegative strict tail
-- statement:
--   Every included tail coefficient is nonnegative, and all coefficients at losses no larger than q are replaced by zero. The finite strict-tail mass therefore cannot be negative.
--
--   **Mathematical statement**
--
--   $$
--   w_s\ge0\Rightarrow T_B(q)\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sec 22.5.3 Definition 22.5 and eq (22.9), library PDF pages 439-442; finite discrete stop-loss representation and VaR atom allocation

import Mathlib
import Definitions.Def_actuarial_tailRiskStrictMass

namespace ActuarialValuation

theorem tailRiskStrictMass_nonneg
  (w : ℕ → ℝ) (bound q : ℕ)
  (hw : ∀ s, 0 ≤ w s) :
  0 ≤ tailRiskStrictMass w bound q := by sorry

end ActuarialValuation
