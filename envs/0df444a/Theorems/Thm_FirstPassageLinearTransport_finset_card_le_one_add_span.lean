-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_finset_card_le_one_add_span
-- name    : FirstPassageLinearTransport.finset_card_le_one_add_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:01:14.227439+00:00
-- url     : https://prove2.me/theorems/e87e2421-2c14-5b97-b537-91ba43561159
-- title:
--   First Passage Linear Transport: finset card le one add span
-- statement:
--   The First Passage Linear Transport construction uses the finset card le one add span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L351-L371
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FirstPassage.lean#L351-L371

import Definitions.Def_FirstPassageLinearTransport_Parity
import Definitions.Def_FirstPassageLinearTransport_FirstPassage
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.finset_card_le_one_add_span (s : Finset ℕ) (hs : s.Nonempty) :
    (s.card : ℚ) ≤
      1 + (s.max' hs : ℚ) - (s.min' hs : ℚ) := by sorry
