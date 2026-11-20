-- Prove2me | Theorems.Thm_DeletionCode_BubbleLocalSpectrum_context_replacement
-- name    : DeletionCode.BubbleLocalSpectrum.context_replacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:20:54.779712+00:00
-- url     : https://prove2.me/theorems/b93e20ca-d7e2-4c4f-8205-d3b9d8797d86
-- title:
--   Bubble Local Spectrum: context replacement
-- statement:
--   Replacing the longer local word by the shorter changes the full spectrum
--   by precisely the local spectrum difference, with arbitrary unchanged context.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L64-L76
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L64-L76

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
import Theorems.Thm_DeletionCode_SpectrumLocalization_context_replacement

set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.BubbleLocalSpectrum.context_replacement {k : ℕ} (bubble : BubbleWord k) (x y : List Bool)
    (g : Gram (windowLength k)) :
    wordSpectrum (listLetters (x ++ (bubble.shortWord ++ y)))
        (x ++ (bubble.shortWord ++ y)).length (windowLength k) g -
      wordSpectrum (listLetters (x ++ (bubble.longWord ++ y)))
        (x ++ (bubble.longWord ++ y)).length (windowLength k) g =
      wordSpectrum (listLetters bubble.shortWord) bubble.shortWord.length (windowLength k) g -
        wordSpectrum (listLetters bubble.longWord) bubble.longWord.length (windowLength k) g := by sorry
