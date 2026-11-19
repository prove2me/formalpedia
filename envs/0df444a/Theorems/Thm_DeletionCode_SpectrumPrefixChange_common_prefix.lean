-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPrefixChange_common_prefix
-- name    : DeletionCode.SpectrumPrefixChange.common_prefix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:40:40.693418+00:00
-- url     : https://prove2.me/theorems/910d1b24-7c32-41bf-9b72-8d3b9109e089
-- title:
--   Spectrum Prefix Change: common prefix
-- statement:
--   The Spectrum Prefix Change construction uses the common prefix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L48-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L48-L54

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.SpectrumPrefixChange.common_prefix (common p q : List Bool) (L : ℕ)
    (hcommon : L - 1 ≤ common.length) :
    Agree (listLetters (common ++ p)) 0 (listLetters (common ++ q)) 0 (L - 1) := by sorry
