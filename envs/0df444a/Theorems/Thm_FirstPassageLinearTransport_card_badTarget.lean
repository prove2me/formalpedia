-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_badTarget
-- name    : FirstPassageLinearTransport.card_badTarget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:08:56.930403+00:00
-- url     : https://prove2.me/theorems/71184377-544f-5757-84b2-d34add0eb5c4
-- title:
--   First Passage Linear Transport: card bad Target
-- statement:
--   The First Passage Linear Transport construction uses the card bad Target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L201-L203
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Pullback.lean#L201-L203

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section

theorem FirstPassageLinearTransport.card_badTarget (S : Set ℕ) (Y : ℕ) :
    (badTarget S Y).card = badCount S Y := by sorry
