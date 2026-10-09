-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityOptimalWeight_nonneg
-- name    : ActuarialValuation.credibilityOptimalWeight_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T10:56:09.845078+00:00
-- url     : https://prove2.me/theorems/4cce2cc4-d516-41e6-82c6-459737ce02a1
-- title:
--   Valid variance components imply nonnegative credibility
-- statement:
--   Nonnegative exposure and heterogeneity produce a nonnegative credibility numerator. With strictly positive total variance denominator, the least-squares factor lies at or above zero.
--
--   **Mathematical statement**
--
--   $$
--   P,\mathrm{EPV},\mathrm{VHM}\ge0\Rightarrow Z\ge0
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityOptimalWeight_nonneg
  (p epv vhm : ℝ) (hp : 0 ≤ p) (he : 0 ≤ epv)
  (hv : 0 ≤ vhm) (hd : 0 < p * vhm + epv) :
  0 ≤ credibilityOptimalWeight p epv vhm := by sorry

end ActuarialValuation
