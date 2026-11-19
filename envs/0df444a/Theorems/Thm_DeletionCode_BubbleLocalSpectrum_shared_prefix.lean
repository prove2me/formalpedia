-- Prove2me | Theorems.Thm_DeletionCode_BubbleLocalSpectrum_shared_prefix
-- name    : DeletionCode.BubbleLocalSpectrum.shared_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:35:47.031946+00:00
-- url     : https://prove2.me/theorems/6a9c5fcf-9313-4c2a-b3a9-3b08a69461f5
-- title:
--   Bubble Local Spectrum: shared prefix
-- statement:
--   Removing the last run bit leaves the first L-1 letters unchanged.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L15-L20
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L15-L20

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.BubbleLocalSpectrum.shared_prefix {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) 0 (listLetters bubble.shortWord) 0
      (windowLength k - 1) := by sorry
