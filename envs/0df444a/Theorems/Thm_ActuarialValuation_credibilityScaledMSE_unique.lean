-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityScaledMSE_unique
-- name    : ActuarialValuation.credibilityScaledMSE_unique
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:25:43.033789+00:00
-- url     : https://prove2.me/theorems/669865e3-a743-44b7-af10-f9615bee8975
-- title:
--   Positive total variance coefficient makes optimum unique
-- statement:
--   With positive total quadratic coefficient, equality of a candidate prediction risk to the minimum forces the squared deviation from the optimal credibility factor to be zero. Thus the least-squares minimiser is unique, including meaningful boundary cases.
--
--   **Mathematical statement**
--
--   $$
--   P\mathrm{MSE}(z)=P\mathrm{MSE}(Z)\Rightarrow z=Z
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityScaledMSE
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityScaledMSE_unique
  (p epv vhm z : ℝ) (hd : 0 < p * vhm + epv)
  (hEq : credibilityScaledMSE p epv vhm z =
    credibilityScaledMSE p epv vhm
      (credibilityOptimalWeight p epv vhm)) :
  z = credibilityOptimalWeight p epv vhm := by sorry

end ActuarialValuation
