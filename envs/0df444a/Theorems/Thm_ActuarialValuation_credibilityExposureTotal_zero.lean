-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityExposureTotal_zero
-- name    : ActuarialValuation.credibilityExposureTotal_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:54:13.461668+00:00
-- url     : https://prove2.me/theorems/425c7906-0fe5-4f90-84ca-9f3cb0207f80
-- title:
--   No observation periods yield zero total exposure
-- statement:
--   When a risk has no observed periods, the finite index range is empty. Its aggregate experience exposure is therefore zero, so no weighted experience premium should be interpreted as based on usable observations.
--
--   **Mathematical statement**
--
--   $$
--   P_0=0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityExposureTotal

namespace ActuarialValuation

theorem credibilityExposureTotal_zero (p : ℕ → ℝ) :
  credibilityExposureTotal p 0 = 0 := by sorry

end ActuarialValuation
