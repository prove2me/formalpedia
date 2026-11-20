-- Prove2me | Theorems.Thm_DeletionCode_RunBubbleConstruction_exists_insertion_bubble
-- name    : DeletionCode.RunBubbleConstruction.exists_insertion_bubble
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:33:35.219202+00:00
-- url     : https://prove2.me/theorems/bff1dcd0-3013-40ed-8de4-1c382477d0fa
-- title:
--   Run Bubble Construction: exists insertion bubble
-- statement:
--   An interior insertion has the same grammar, with the source and
--   target paths reversed. The run bit is the actual inserted bit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L215-L258
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RunBubbleConstruction.lean#L215-L258

import Definitions.Def_DeletionCode_MaximalRuns
import Definitions.Def_DeletionCode_RunBubbleConstruction
set_option autoImplicit true
open DeletionCode DeletionCode.RunBubbleConstruction
open Windows HeaderRecovery CatalogueWords MaximalRuns

theorem DeletionCode.RunBubbleConstruction.exists_insertion_bubble (word : List Bool) (pos k : ℕ) (bit : Bool)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : LocalBubble k word (word.take pos ++ bit :: word.drop pos) pos .insertion,
      p.bubble.bit = bit := by sorry
