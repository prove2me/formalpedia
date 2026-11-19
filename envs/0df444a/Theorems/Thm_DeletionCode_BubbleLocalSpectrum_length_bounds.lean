-- Prove2me | Theorems.Thm_DeletionCode_BubbleLocalSpectrum_length_bounds
-- name    : DeletionCode.BubbleLocalSpectrum.length_bounds
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:38:03.566419+00:00
-- url     : https://prove2.me/theorems/97f419cd-19ec-432a-a58c-443ef0e59f87
-- title:
--   Bubble Local Spectrum: length bounds
-- statement:
--   The Bubble Local Spectrum construction uses the length bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L53-L60
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleLocalSpectrum.lean#L53-L60

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_BubbleLocalSpectrum
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleLocalSpectrum
open Windows HeaderRecovery CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.BubbleLocalSpectrum.length_bounds {k : ℕ} (bubble : BubbleWord k) :
    windowLength k ≤ bubble.longWord.length + 1 ∧
      windowLength k ≤ bubble.shortWord.length + 1 := by sorry
