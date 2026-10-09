-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualRisk_nonneg
-- name    : ActuarialValuation.decrementAnnualRisk_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:12:40.34651+00:00
-- url     : https://prove2.me/theorems/3291d1ba-166c-4eb3-a0e2-6f55181c2810
-- title:
--   Annual competing-risk allocation is a nonnegative variance
-- statement:
--   Conditional on survival to the start of the year, cause outcomes have nonnegative probabilities with total probability no more than one; the remaining probability is survival. The annual risk expression is the variance of a categorical benefit random variable and is consequently nonnegative.
--
--   **Mathematical statement**
--
--   $$
--   A_t\ge0
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementAnnualRisk
import Definitions.Def_actuarial_decrementYearMass
import Definitions.Def_actuarial_decrementTailMass

namespace ActuarialValuation

theorem decrementAnnualRisk_nonneg {C : Type*} [Fintype C]
  (w rho : ℕ → C → ℝ) (t : ℕ)
  (hw : ∀ c, 0 ≤ w t c)
  (hS : 0 < decrementTailMass w t)
  (hD : decrementYearMass w t ≤ decrementTailMass w t) :
  0 ≤ decrementAnnualRisk w rho t := by sorry

end ActuarialValuation
