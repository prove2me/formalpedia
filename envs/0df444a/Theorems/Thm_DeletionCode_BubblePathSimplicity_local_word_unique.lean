-- Prove2me | Theorems.Thm_DeletionCode_BubblePathSimplicity_local_word_unique
-- name    : DeletionCode.BubblePathSimplicity.local_word_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:24:15.384459+00:00
-- url     : https://prove2.me/theorems/8a844697-97da-48aa-96e2-564fb82d37cc
-- title:
--   Bubble Path Simplicity: local word unique
-- statement:
--   A concrete local list in a valid one-edit output inherits (L-1)-uniqueness.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L32-L39
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubblePathSimplicity.lean#L32-L39

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubblePathSimplicity
set_option autoImplicit true
open DeletionCode DeletionCode.BubblePathSimplicity
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubblePathSimplicity.local_word_unique {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e : Edit) (he : e.Valid n)
    (word : List Bool) (s : ℕ)
    (hbound : s + word.length ≤ e.outputLength n)
    (hocc : Agree (listLetters word) 0 (e.word x) s word.length) :
    KUnique (listLetters word) word.length (windowLength k - 1) := by sorry
