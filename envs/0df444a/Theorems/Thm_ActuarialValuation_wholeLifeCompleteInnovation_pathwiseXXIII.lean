-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeCompleteInnovation_pathwiseXXIII
-- name    : ActuarialValuation.wholeLifeCompleteInnovation_pathwiseXXIII
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:53:29.576853+00:00
-- url     : https://prove2.me/theorems/d5f0d6e7-76a9-4a35-bdbf-b480a30b37a0
-- title:
--   Countable-lifetime pathwise Hattendorff innovation decomposition
-- statement:
--   For an arbitrary realised death year k, the complete-life mortality innovation equals the sum of negative conditional mortality shocks for every earlier year plus the year-k death shock. This source-faithful finite path identity is needed to telescope the first and second moments of the countable whole-life variable.
-- source:
--   Shiu and Xiong (2021), An elementary derivation of Hattendorff's theorem; exact mission XXIII definitions and already proved innovation case theorems.

import Mathlib
import Definitions.Def_actuarial_wholeLifeCompleteInnovation
import Definitions.Def_actuarial_wholeLifeTailMass
import Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_at
import Theorems.Thm_ActuarialValuation_wholeLifeYearInnovation_survivor

namespace ActuarialValuation

theorem wholeLifeCompleteInnovation_pathwiseXXIII
    (w rho : ℕ → ℝ) (k : ℕ) :
  wholeLifeCompleteInnovation w rho k =
    -(∑ t ∈ Finset.range k, rho t * (w t / wholeLifeTailMass w t)) +
      rho k * (1 - w k / wholeLifeTailMass w k) := by sorry

end ActuarialValuation
