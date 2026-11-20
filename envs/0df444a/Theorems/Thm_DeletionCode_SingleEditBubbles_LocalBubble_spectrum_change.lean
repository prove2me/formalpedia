-- Prove2me | Theorems.Thm_DeletionCode_SingleEditBubbles_LocalBubble_spectrum_change
-- name    : DeletionCode.SingleEditBubbles.LocalBubble.spectrum_change
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:42:00.687062+00:00
-- url     : https://prove2.me/theorems/f885bd77-9caa-4e17-92fe-e93bfb678190
-- title:
--   Local Bubble: spectrum change
-- statement:
--   The full spectrum change equals the actual positive-minus-negative local
--   word spectra, not just an abstract signed vector with the right support.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L29-L35
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SingleEditBubbles.lean#L29-L35

import Definitions.Def_DeletionCode_RunBubbleConstruction
import Definitions.Def_DeletionCode_BubbleContextGeometry
import Definitions.Def_DeletionCode_TraceSeparation
import Definitions.Def_DeletionCode_SingleEditBubbles
set_option autoImplicit true
open DeletionCode DeletionCode.SingleEditBubbles
open Windows HeaderRecovery CatalogueWords SignedSupport
open RunBubbleConstruction BubbleContextGeometry TraceSeparation
open DeletionCode.SingleEditBubbles.LocalBubble
variable {k pos : ℕ} {source target : List Bool} {orientation : Orientation}

theorem DeletionCode.SingleEditBubbles.LocalBubble.spectrum_change (p : LocalBubble k source target pos orientation) :
    wordSpectrum (listLetters target) target.length (windowLength k) -
      wordSpectrum (listLetters source) source.length (windowLength k) =
      wordSpectrum (listLetters p.bubble.positiveWord) p.bubble.positiveWord.length (windowLength k) -
        wordSpectrum (listLetters p.bubble.negativeWord) p.bubble.negativeWord.length (windowLength k) := by sorry
