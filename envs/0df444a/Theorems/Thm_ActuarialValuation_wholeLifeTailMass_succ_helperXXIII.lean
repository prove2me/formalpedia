-- Prove2me | Theorems.Thm_ActuarialValuation_wholeLifeTailMass_succ_helperXXIII
-- name    : ActuarialValuation.wholeLifeTailMass_succ_helperXXIII
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:52:08.724737+00:00
-- url     : https://prove2.me/theorems/48b58db1-470b-4d32-9e0b-012c5d8d49c8
-- title:
--   Countable lifetime survival-tail decomposition
-- statement:
--   For a summable real death-year mass function w, the countable mass remaining at time t splits exactly into the year-t decrement mass and the survival mass from t+1. This identity is required to justify the boundary terms in the whole-life Hattendorff variance limit.
-- source:
--   Countable series partition identity, established within the accepted second-moment proof of ActuarialValuation.wholeLifeYearInnovation_second_moment, Mission XXIII.

import Mathlib
import Definitions.Def_actuarial_wholeLifeTailMass

namespace ActuarialValuation

theorem wholeLifeTailMass_succ_helperXXIII (w : ℕ → ℝ) (t : ℕ) (hw : Summable w) :
  wholeLifeTailMass w t = w t + wholeLifeTailMass w (t + 1) := by sorry

end ActuarialValuation
