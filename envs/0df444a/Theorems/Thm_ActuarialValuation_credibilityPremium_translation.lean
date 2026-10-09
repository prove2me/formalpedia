-- Prove2me | Theorems.Thm_ActuarialValuation_credibilityPremium_translation
-- name    : ActuarialValuation.credibilityPremium_translation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-09T11:10:55.817933+00:00
-- url     : https://prove2.me/theorems/986d0599-d9f2-48c9-acd1-482400c8ac28
-- title:
--   Adding the same currency amount to both means translates the premium
-- statement:
--   When both the collective estimate and observed per-unit losses are shifted by the same deterministic amount, the credibility premium shifts by that amount. The shift is not multiplied by the credibility factor because the two weights sum to one.
--
--   **Mathematical statement**
--
--   $$
--   \hat\mu(\mu+c,\bar X+c)=\hat\mu(\mu,\bar X)+c
--   $$
-- source:
--   S David Promislow (2015), Fundamentals of Actuarial Mathematics (3rd ed), sections 24.5.2-24.5.3 equations (24.13)-(24.16), library PDF pages 489-491; weighted Buehlmann-Straub model and least-squares premium; https://openacttexts.github.io/LDAVer2/ChapCredibility.html

import Mathlib
import Definitions.Def_actuarial_credibilityPremium

namespace ActuarialValuation

theorem credibilityPremium_translation
  (mu observed z shift : ℝ) :
  credibilityPremium (mu + shift) (observed + shift) z =
    credibilityPremium mu observed z + shift := by sorry

end ActuarialValuation
