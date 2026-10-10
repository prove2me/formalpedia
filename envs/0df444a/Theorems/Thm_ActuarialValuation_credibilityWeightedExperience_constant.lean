-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityWeightedExperience_constant
-- name    : ActuarialValuation.credibilityWeightedExperience_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:55:18.010424+00:00
-- url     : https://prove2.me/theorems/6ec1f548-f991-489e-b367-53dd8e08a5da
-- title:
--   Constant observations have that same weighted mean
-- statement:
--   When all reported per-unit loss levels equal a common constant c, their weighted average remains exactly c provided total exposure is nonzero. This holds independently of the balance between periods, including different reporting volumes.
--
--   **Mathematical statement**
--
--   $$
--   X_i=c,\ P\ne0\Rightarrow \bar X_P=c
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityWeightedExperience
import Definitions.Def_actuarial_credibilityExposureTotal

namespace ActuarialValuation

theorem credibilityWeightedExperience_constant
  (p : ℕ → ℝ) (n : ℕ) (c : ℝ)
  (hpos : credibilityExposureTotal p n ≠ 0) :
  credibilityWeightedExperience p (fun _ => c) n = c := by sorry

end ActuarialValuation
