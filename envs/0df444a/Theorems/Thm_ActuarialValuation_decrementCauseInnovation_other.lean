-- Prove2me | Theorems.Thm_ActuarialValuation_decrementCauseInnovation_other
-- name    : ActuarialValuation.decrementCauseInnovation_other
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:06:31.680989+00:00
-- url     : https://prove2.me/theorems/464b93c5-3702-48fd-96ad-632cba742c1a
-- title:
--   Another same-year cause gives a negative innovation
-- statement:
--   If the policy terminates through a different cause in the same year, the cause-c event did not occur but the insurer was exposed to it. The cause-c surprise is the negative of its own conditional incidence.
--
--   **Mathematical statement**
--
--   $$
--   d\ne c\Longrightarrow I_{t,c}(t,d)=-q_{t,c}
--   $$
-- source:
--   Shiu and Xiong (2021), DOI https://doi.org/10.1007/s13385-020-00256-9; original multiple-decrement and cause-covariance extension in this mission

import Mathlib
import Definitions.Def_actuarial_decrementCauseInnovation
import Definitions.Def_actuarial_decrementTailMass

namespace ActuarialValuation

theorem decrementCauseInnovation_other {C : Type*} [Fintype C]
  (w : ℕ → C → ℝ) (t : ℕ) (c d : C) (h : d ≠ c) :
  decrementCauseInnovation w t c t d =
    -(w t c / decrementTailMass w t) := by sorry

end ActuarialValuation
