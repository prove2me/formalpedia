-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_insertion_bubble
-- name    : DeletionCode.SingleEditBubbles.insertion_bubble
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:20.230412+00:00
-- url     : https://prove2.me/theorems/1134ef7a-7fd6-4827-9eae-78aec0caae64
-- title:
--   Single Edit Bubbles: insertion bubble
-- statement:
--   The insertion version keeps the inserted bit and constructs the exact
--   source and target presentations, including the case of a newly created run.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L84-L97
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L84-L97

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation

theorem DeletionCode.SingleEditBubbles.insertion_bubble (word : List Bool) (pos k : ℕ) (bit : Bool) (hk : 1 ≤ k)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : RunBubbleConstruction.LocalBubble k word
        (word.take pos ++ bit :: word.drop pos) pos .insertion,
      p.bubble.bit = bit ∧ Geometry p.bubble ∧
      wordSpectrum (listLetters (word.take pos ++ bit :: word.drop pos))
          (word.take pos ++ bit :: word.drop pos).length (windowLength k) -
        wordSpectrum (listLetters word) word.length (windowLength k) =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by sorry
