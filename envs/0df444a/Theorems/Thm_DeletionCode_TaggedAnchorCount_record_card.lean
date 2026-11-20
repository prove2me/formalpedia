-- Prove2me | Theorems.Thm_DeletionCode_TaggedAnchorCount_record_card
-- name    : DeletionCode.TaggedAnchorCount.record_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:45:43.770034+00:00
-- url     : https://prove2.me/theorems/5ede09fe-cdff-479c-a66d-4d5e0947c5c9
-- title:
--   Tagged Anchor Count: record card
-- statement:
--   The Tagged Anchor Count construction uses the record card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TaggedAnchorCount.lean#L18-L20
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TaggedAnchorCount.lean#L18-L20

import Definitions.Def_DeletionCode_CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import Definitions.Def_DeletionCode_TaggedAnchorCount
set_option autoImplicit true
open DeletionCode DeletionCode.TaggedAnchorCount

theorem DeletionCode.TaggedAnchorCount.record_card (n r : ℕ) : Fintype.card (Record n r) = n ^ r * 4 ^ r := by sorry
