-- Prove2me | Theorems.Thm_DeletionCode_BubbleLocalSpectrum_shared_suffix
-- name    : DeletionCode.BubbleLocalSpectrum.shared_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:35:49.508426+00:00
-- url     : https://prove2.me/theorems/99ce0e3b-62be-47bd-80d0-305e47f60a12
-- title:
--   Bubble Local Spectrum: shared suffix
-- statement:
--   The two local words end in the same actual word d^(rho-1) B.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L23-L51
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L23-L51

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.BubbleLocalSpectrum.shared_suffix {k : ℕ} (bubble : BubbleWord k) :
    Agree (listLetters bubble.longWord) (bubble.longWord.length + 1 - windowLength k)
      (listLetters bubble.shortWord) (bubble.shortWord.length + 1 - windowLength k)
      (windowLength k - 1) := by sorry
