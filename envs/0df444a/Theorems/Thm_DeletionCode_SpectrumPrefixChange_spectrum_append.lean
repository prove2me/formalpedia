-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPrefixChange_spectrum_append
-- name    : DeletionCode.SpectrumPrefixChange.spectrum_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:36.103374+00:00
-- url     : https://prove2.me/theorems/7d1fd98b-e229-45b1-ad8f-57b4017ef330
-- title:
--   Spectrum Prefix Change: spectrum append
-- statement:
--   The Spectrum Prefix Change construction uses the spectrum append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L18-L25
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L18-L25

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.SpectrumPrefixChange.spectrum_append (pre p : List Bool) (L : ℕ) (hp : L ≤ p.length + 1)
    (g : Gram L) :
    spectrum (pre ++ p) L g =
      windowSum (listLetters (pre ++ p)) L 0 pre.length g + spectrum p L g := by sorry
