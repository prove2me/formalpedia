-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityBuehlmannStraub_fundamental
-- name    : ActuarialValuation.credibilityBuehlmannStraub_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:26:41.863162+00:00
-- url     : https://prove2.me/theorems/cd58725e-6e20-4053-a629-f7f4f8ab841a
-- title:
--   Admissible and least-squares-optimal Bühlmann–Straub credibility
-- statement:
--   The capstone proves that the Bühlmann–Straub credibility factor belongs to the admissible unit interval and minimises the exposure-scaled least-squares prediction error against every alternative weight. It keeps expected process variance separate from variance of hypothetical means and excludes an undefined zero-denominator case.
--
--   **Mathematical statement**
--
--   $$
--   0\le Z\le1,\quad\forall z:\ P\mathrm{MSE}(Z)\le P\mathrm{MSE}(z)
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityOptimalWeight
import Definitions.Def_actuarial_credibilityScaledMSE

namespace ActuarialValuation

theorem credibilityBuehlmannStraub_fundamental
  (p epv vhm : ℝ)
  (hp : 0 ≤ p) (he : 0 ≤ epv) (hv : 0 ≤ vhm)
  (hd : 0 < p * vhm + epv) :
  (0 ≤ credibilityOptimalWeight p epv vhm ∧
     credibilityOptimalWeight p epv vhm ≤ 1) ∧
  (∀ z : ℝ, credibilityScaledMSE p epv vhm
       (credibilityOptimalWeight p epv vhm) ≤
     credibilityScaledMSE p epv vhm z) := by sorry

end ActuarialValuation
