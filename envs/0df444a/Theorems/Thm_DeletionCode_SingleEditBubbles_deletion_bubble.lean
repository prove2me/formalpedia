-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_deletion_bubble
-- name    : DeletionCode.SingleEditBubbles.deletion_bubble
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:28.506148+00:00
-- url     : https://prove2.me/theorems/5f2e1259-4dcd-4acd-9eeb-1a86cc95ee04
-- title:
--   Single Edit Bubbles: deletion bubble
-- statement:
--   A real interior deletion gives a bubble whose geometry and exact spectrum
--   identity are both derived. No prechosen run, flanks, or paths are inputs.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L69-L80
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L69-L80

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation

theorem DeletionCode.SingleEditBubbles.deletion_bubble (word : List Bool) (pos k : ℕ) (hk : 1 ≤ k)
    (hx : KUnique (listLetters word) word.length k)
    (hleft : 4 * windowLength k ≤ pos)
    (hright : pos + 4 * windowLength k ≤ word.length) :
    ∃ p : RunBubbleConstruction.LocalBubble k word (word.eraseIdx pos) pos .deletion,
      Geometry p.bubble ∧
      wordSpectrum (listLetters (word.eraseIdx pos)) (word.eraseIdx pos).length (windowLength k) -
        wordSpectrum (listLetters word) word.length (windowLength k) =
        wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
          wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by sorry
