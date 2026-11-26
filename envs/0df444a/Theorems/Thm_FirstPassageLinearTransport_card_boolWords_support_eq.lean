-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_card_boolWords_support_eq
-- name    : FirstPassageLinearTransport.card_boolWords_support_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:34:37.220818+00:00
-- url     : https://prove2.me/theorems/f6d057e9-8f6a-4f4e-bd2b-85d77c32187a
-- title:
--   First Passage Linear Transport: card bool Words support eq
-- statement:
--   The First Passage Linear Transport construction uses the card bool Words support eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1471-L1486
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1471-L1486

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.card_boolWords_support_eq (n k : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).filter
      (fun v => (boolSupport v).card = k)).card = n.choose k := by sorry
