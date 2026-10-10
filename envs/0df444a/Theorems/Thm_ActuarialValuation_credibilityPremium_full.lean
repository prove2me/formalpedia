-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityPremium_full
-- name    : ActuarialValuation.credibilityPremium_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T11:01:31.556509+00:00
-- url     : https://prove2.me/theorems/22477719-c0d5-4633-837f-1e6b730bbe97
-- title:
--   Full credibility returns observed experience
-- statement:
--   A factor of one places all weight on the risk's observed experience mean and none on the collective mean. The result is an exact algebraic boundary for the credibility-weighted premium.
--
--   **Mathematical statement**
--
--   $$
--   \hat\mu(1)=\bar X
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityPremium

namespace ActuarialValuation

theorem credibilityPremium_full (mu observed : ℝ) :
  credibilityPremium mu observed 1 = observed := by sorry

end ActuarialValuation
