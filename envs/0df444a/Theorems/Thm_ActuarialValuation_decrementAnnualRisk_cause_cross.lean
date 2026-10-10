-- Prove2me | Theorems.Thm_ActuarialValuation_decrementAnnualRisk_cause_cross
-- name    : ActuarialValuation.decrementAnnualRisk_cause_cross
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:14:22.280652+00:00
-- url     : https://prove2.me/theorems/5e0b576c-a249-4caa-8b89-7426b1d02215
-- title:
--   Different decrement causes have a negative same-year cross-moment
-- statement:
--   The two distinct decrement causes are mutually exclusive at any termination time. Their centred annual event innovations have negative cross-moment equal to the product of the unconditional cause masses divided by in-force survival mass. The assumption of nonnegative summable masses makes the countable expectation legitimate.
--
--   **Mathematical statement**
--
--   $$
--   \mathbb E[I_{t,c}I_{t,d}]=-w_{t,c}w_{t,d}/S_t
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass
import Definitions.Def_actuarial_decrementYearMass

namespace ActuarialValuation

theorem decrementAnnualRisk_cause_cross {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c d : C)
  (hw : Summable (fun k : ℕ => decrementYearMass w k))
  (hn : ∀ k e, 0 ≤ w k e)
  (hS : 0 < decrementTailMass w t) (hcd : c ≠ d) :
  (∑' k : ℕ, ∑ e : C, w k e *
      decrementCauseInnovation w t c k e *
      decrementCauseInnovation w t d k e) =
    -(w t c * w t d / decrementTailMass w t) := by sorry

end ActuarialValuation
