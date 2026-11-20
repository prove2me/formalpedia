-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPrefixChange_common_suffix_change
-- name    : DeletionCode.SpectrumPrefixChange.common_suffix_change
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:40:46.702449+00:00
-- url     : https://prove2.me/theorems/3c9922a2-dd92-4ae4-a02c-575ada528bbb
-- title:
--   Spectrum Prefix Change: common suffix change
-- statement:
--   An edit after a common long enough suffix has the same increment for
--   both earlier prefixes. No condition on the words following the edit is needed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L58-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L58-L70

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.SpectrumPrefixChange.common_suffix_change (a b common p q : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hcommon : L - 1 ≤ common.length) (g : Gram L) :
    spectrum ((b ++ common) ++ q) L g - spectrum ((b ++ common) ++ p) L g =
      spectrum ((a ++ common) ++ q) L g - spectrum ((a ++ common) ++ p) L g := by sorry
