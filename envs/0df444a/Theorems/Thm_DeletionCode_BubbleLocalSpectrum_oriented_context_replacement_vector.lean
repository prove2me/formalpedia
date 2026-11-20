-- Prove2me | Theorems.Thm_DeletionCode_BubbleLocalSpectrum_oriented_context_replacement_vector
-- name    : DeletionCode.BubbleLocalSpectrum.oriented_context_replacement_vector
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:38:12.324562+00:00
-- url     : https://prove2.me/theorems/0e627d7b-e550-4162-9fc9-c6c8ea187344
-- title:
--   Bubble Local Spectrum: oriented context replacement vector
-- statement:
--   Function equality of the actual signed integer spectrum vectors.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L97-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L97-L105

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.BubbleLocalSpectrum.oriented_context_replacement_vector {k : ℕ} (bubble : BubbleWord k) (x y : List Bool) :
    wordSpectrum (listLetters (x ++ (bubble.positiveWord ++ y)))
        (x ++ (bubble.positiveWord ++ y)).length (windowLength k) -
      wordSpectrum (listLetters (x ++ (bubble.negativeWord ++ y)))
        (x ++ (bubble.negativeWord ++ y)).length (windowLength k) =
      wordSpectrum (listLetters bubble.positiveWord) bubble.positiveWord.length (windowLength k) -
        wordSpectrum (listLetters bubble.negativeWord) bubble.negativeWord.length (windowLength k) := by sorry
