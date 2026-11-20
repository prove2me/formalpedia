-- Prove2me | Theorems.Thm_DeletionCode_TaggedAnchorCount_bad_record_card_le
-- name    : DeletionCode.TaggedAnchorCount.bad_record_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:45:46.268787+00:00
-- url     : https://prove2.me/theorems/b43748d8-159a-4e26-be3f-a56bb04327ae
-- title:
--   Tagged Anchor Count: bad record card le
-- statement:
--   The Tagged Anchor Count construction uses the bad record card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TaggedAnchorCount.lean#L33-L43
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TaggedAnchorCount.lean#L33-L43

import Definitions.Def_DeletionCode_CloseAnchorCount
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum
import Definitions.Def_DeletionCode_TaggedAnchorCount
set_option autoImplicit true
open DeletionCode DeletionCode.TaggedAnchorCount

theorem DeletionCode.TaggedAnchorCount.bad_record_card_le (n r m B : ℕ) :
    Nat.card {rec : Record n r // Bad m B rec} ≤
      r * (r + 2) * (2 * B) * n ^ (r - 1) * 4 ^ r := by sorry
