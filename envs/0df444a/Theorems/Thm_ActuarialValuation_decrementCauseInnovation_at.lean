-- Prove2me | Theorems.Thm_ActuarialValuation_decrementCauseInnovation_at
-- name    : ActuarialValuation.decrementCauseInnovation_at
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:05:39.016764+00:00
-- url     : https://prove2.me/theorems/9c814865-ef63-48b3-91f1-289a76ca423d
-- title:
--   Innovation of the observed termination cause
-- statement:
--   When the actual cause is c and termination occurs in year t, its event indicator and in-force indicator both equal one. Its surprise therefore equals one minus the conditional probability of this particular cause.
--
--   **Mathematical statement**
--
--   $$
--   I_{t,c}(t,c)=1-q_{t,c}
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass

namespace ActuarialValuation

theorem decrementCauseInnovation_at {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c : C) :
  decrementCauseInnovation w t c t c =
    1 - w t c / decrementTailMass w t := by sorry

end ActuarialValuation
