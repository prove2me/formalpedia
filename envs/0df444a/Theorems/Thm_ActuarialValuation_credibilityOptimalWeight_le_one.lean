-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityOptimalWeight_le_one
-- name    : ActuarialValuation.credibilityOptimalWeight_le_one
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:56:54.58352+00:00
-- url     : https://prove2.me/theorems/4e5ee75b-a856-42ee-8c9f-48ab6b485a57
-- title:
--   Valid variance components bound credibility by one
-- statement:
--   The expected process variance is nonnegative, so the product of exposure and hypothetical-mean variance cannot exceed their positive sum. Consequently the credibility factor is at most one.
--
--   **Mathematical statement**
--
--   $$
--   0\le Z\le1
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityOptimalWeight_le_one
  (p epv vhm : ℝ) (hp : 0 ≤ p) (he : 0 ≤ epv)
  (hv : 0 ≤ vhm) (hd : 0 < p * vhm + epv) :
  credibilityOptimalWeight p epv vhm ≤ 1 := by sorry

end ActuarialValuation
