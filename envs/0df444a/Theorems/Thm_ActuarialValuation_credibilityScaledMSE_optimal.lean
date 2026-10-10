-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityScaledMSE_optimal
-- name    : ActuarialValuation.credibilityScaledMSE_optimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:24:40.00599+00:00
-- url     : https://prove2.me/theorems/3130ee95-8b4f-4cfb-93fe-b5923d3192e9
-- title:
--   Variance-derived credibility factor globally minimises linear prediction error
-- statement:
--   The predictor with variance-derived credibility factor achieves no greater expected squared error than any alternative real credibility weight. The proof follows from square completion, not from asserting that an arbitrary Bayesian posterior is always linear.
--
--   **Mathematical statement**
--
--   $$
--   P\mathrm{MSE}(Z)\le P\mathrm{MSE}(z)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityScaledMSE
import Definitions.Def_actuarial_credibilityOptimalWeight

namespace ActuarialValuation

theorem credibilityScaledMSE_optimal
  (p epv vhm z : ℝ)
  (hp : 0 ≤ p) (he : 0 ≤ epv) (hv : 0 ≤ vhm)
  (hd : 0 < p * vhm + epv) :
  credibilityScaledMSE p epv vhm
      (credibilityOptimalWeight p epv vhm) ≤
    credibilityScaledMSE p epv vhm z := by sorry

end ActuarialValuation
