-- Prove2me | Theorems.Thm_DeletionCode_RedundancyBounds_card_positive
-- name    : DeletionCode.RedundancyBounds.card_positive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:37:50.008219+00:00
-- url     : https://prove2.me/theorems/ab30777b-d00c-4fb1-a3d2-e134394f6b45
-- title:
--   Redundancy Bounds: card positive
-- statement:
--   The Redundancy Bounds construction uses the card positive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L16-L22
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RedundancyBounds.lean#L16-L22

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery

theorem DeletionCode.RedundancyBounds.card_positive (n Q : ℕ) (C : Finset (Bits n))
    (hcard : 2 ^ n ≤ 8 * Q * C.card) : 0 < C.card := by sorry
