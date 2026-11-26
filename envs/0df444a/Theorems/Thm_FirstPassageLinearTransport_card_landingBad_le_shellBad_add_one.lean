-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_landingBad_le_shellBad_add_one
-- name    : FirstPassageLinearTransport.card_landingBad_le_shellBad_add_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:13:58.785214+00:00
-- url     : https://prove2.me/theorems/fb84dba6-88d8-5f21-bb59-6ec4ce8a17a1
-- title:
--   First Passage Linear Transport: card landing Bad le shell Bad add one
-- statement:
--   The First Passage Linear Transport construction uses the card landing Bad le shell Bad add one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L61-L65
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstBadEnvelope.lean#L61-L65

import Definitions.Def_FirstPassageLinearTransport_AdjustableBarrierDensity
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.card_landingBad_le_shellBad_add_one
    {q : ℕ} (hq : 1 ≤ q) (t : ℝ) :
    (landingBad q t).card ≤ (shellInitialWindowBad (q - 1) t).card + 1 := by sorry
