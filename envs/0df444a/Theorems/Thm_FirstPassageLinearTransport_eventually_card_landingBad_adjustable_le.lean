-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_eventually_card_landingBad_adjustable_le
-- name    : FirstPassageLinearTransport.eventually_card_landingBad_adjustable_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:16:07.645085+00:00
-- url     : https://prove2.me/theorems/d0650252-4f7c-4c81-b2c6-df1f23c7c9a5
-- title:
--   First Passage Linear Transport: eventually card landing Bad adjustable le
-- statement:
--   Entropy-sharp target-cardinality bound for the actual first-passage
--   landing band, including its single upper power-of-two endpoint.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L69-L102
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L69-L102

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.eventually_card_landingBad_adjustable_le
    {lambda t : ℝ} (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda < 1)
    (ht0 : 0 < t) (htA : t < a0) :
    ∀ᶠ q : ℕ in Filter.atTop,
      ((landingBad q t).card : ℝ) ≤
        1 + (2 : ℝ) ^ q *
          Real.exp (-(((q - 1 : ℕ) : ℝ) *
            binaryBarrierRate (adjustableBarrierDisplacement lambda t))) := by sorry
