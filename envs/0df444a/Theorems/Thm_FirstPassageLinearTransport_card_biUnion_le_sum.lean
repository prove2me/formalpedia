-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_biUnion_le_sum
-- name    : FirstPassageLinearTransport.card_biUnion_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:00:03.913389+00:00
-- url     : https://prove2.me/theorems/e15d298f-3c84-5070-b75c-32b58caca6b1
-- title:
--   First Passage Linear Transport: card bi Union le sum
-- statement:
--   The First Passage Linear Transport construction uses the card bi Union le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L88-L99
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/Transport.lean#L88-L99

import Definitions.Def_FirstPassageLinearTransport_FirstPassage
import Definitions.Def_FirstPassageLinearTransport_Transport
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.card_biUnion_le_sum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a ∈ s, (f a).card := by sorry
