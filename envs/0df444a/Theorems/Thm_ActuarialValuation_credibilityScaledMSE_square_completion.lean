-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityScaledMSE_square_completion
-- name    : ActuarialValuation.credibilityScaledMSE_square_completion
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:24:10.427377+00:00
-- url     : https://prove2.me/theorems/ea1e9c7c-197f-4255-8df9-9e0abd4c54fa
-- title:
--   Least-squares credibility risk completes to a nonnegative square
-- statement:
--   Completing the quadratic prediction error around the ratio of signal variance to total variance separates its fixed minimum from a squared deviation. Under a positive denominator this deviation penalty is nonnegative and vanishes exactly at the optimal factor.
--
--   **Mathematical statement**
--
--   $$
--   P\mathrm{MSE}(z)=\frac{P\,\mathrm{VHM}\,\mathrm{EPV}}{P\,\mathrm{VHM}+\mathrm{EPV}}+(P\,\mathrm{VHM}+\mathrm{EPV})(z-Z)^2
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityScaledMSE
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityScaledMSE_square_completion
  (p epv vhm z : ℝ) (hd : p * vhm + epv ≠ 0) :
  credibilityScaledMSE p epv vhm z =
    (p * vhm * epv) / (p * vhm + epv) +
    (p * vhm + epv) *
      (z - credibilityOptimalWeight p epv vhm) ^ 2 := by sorry

end ActuarialValuation
