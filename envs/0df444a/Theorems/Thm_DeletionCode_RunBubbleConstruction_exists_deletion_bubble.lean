-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_exists_deletion_bubble
-- name    : DeletionCode.RunBubbleConstruction.exists_deletion_bubble
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:33:31.427368+00:00
-- url     : https://prove2.me/theorems/64bdb13f-df00-48fe-9be9-d1ccadb16ed0
-- title:
--   Run Bubble Construction: exists deletion bubble
-- statement:
--   Every sufficiently interior deletion in a k-unique finite source has
--   the catalogue word grammar, including the opposite boundary bits. The
--   deleted position may be anywhere in its extracted maximal run.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L164-L211
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L164-L211

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns

theorem DeletionCode.RunBubbleConstruction.exists_deletion_bubble (word : List Bool) (pos k : ℕ)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    Nonempty (LocalBubble k word (word.eraseIdx pos) pos .deletion) := by sorry
