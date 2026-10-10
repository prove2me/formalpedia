-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityPremium_collective
-- name    : ActuarialValuation.credibilityPremium_collective
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T10:58:41.205923+00:00
-- url     : https://prove2.me/theorems/f701a4d4-1f5e-402f-8a4e-340b34107ac4
-- title:
--   Zero credibility returns the collective premium
-- statement:
--   A factor of zero ignores experience for the particular insured risk and uses the collective manual estimate. This boundary is required for an individual with no distinguishable hypothetical risk mean.
--
--   **Mathematical statement**
--
--   $$
--   \hat\mu(0)=\mu
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityPremium

namespace ActuarialValuation

theorem credibilityPremium_collective (mu observed : ℝ) :
  credibilityPremium mu observed 0 = mu := by sorry

end ActuarialValuation
