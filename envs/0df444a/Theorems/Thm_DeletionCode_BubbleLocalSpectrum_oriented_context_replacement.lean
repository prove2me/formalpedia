-- Prove2me | Theorems.Thm_DeletionCode_BubbleLocalSpectrum_oriented_context_replacement
-- name    : DeletionCode.BubbleLocalSpectrum.oriented_context_replacement
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:38:03.997304+00:00
-- url     : https://prove2.me/theorems/c890488c-bd6e-4235-b8b6-20844a634b59
-- title:
--   Bubble Local Spectrum: oriented context replacement
-- statement:
--   The local replacement formula uses the actual negative and positive
--   grammar words in both deletion and insertion orientations.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L80-L94
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L80-L94

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.BubbleLocalSpectrum.oriented_context_replacement {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) g := by sorry
