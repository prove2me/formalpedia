-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityExposureTotal_succ
-- name    : ActuarialValuation.credibilityExposureTotal_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:54:45.138761+00:00
-- url     : https://prove2.me/theorems/ec08ba6a-f79b-4a7e-b210-080ac1dd4d8d
-- title:
--   Adding a period adds its individual exposure
-- statement:
--   The total weight for n+1 periods equals the previous total plus the new period's exposure. This allows an incremental credibility calculation when a further year's insurance experience becomes available.
--
--   **Mathematical statement**
--
--   $$
--   P_{n+1}=P_n+p_n
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityExposureTotal

namespace ActuarialValuation

theorem credibilityExposureTotal_succ
  (p : ℕ → ℝ) (n : ℕ) :
  credibilityExposureTotal p (n + 1) =
    credibilityExposureTotal p n + p n := by sorry

end ActuarialValuation
