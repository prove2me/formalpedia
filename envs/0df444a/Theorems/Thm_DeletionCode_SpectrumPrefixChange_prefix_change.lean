-- Prove2me | Theorems.Thm_DeletionCode_SpectrumPrefixChange_prefix_change
-- name    : DeletionCode.SpectrumPrefixChange.prefix_change
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:40:41.829048+00:00
-- url     : https://prove2.me/theorems/0fda95e3-9783-4ceb-91af-061c54a7a900
-- title:
--   Spectrum Prefix Change: prefix change
-- statement:
--   Only the first L-1 letters can affect windows starting before a local word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L28-L46
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SpectrumPrefixChange.lean#L28-L46

import Definitions.Def_DeletionCode_SpectrumLocalization
import Definitions.Def_DeletionCode_SpectrumPrefixChange
set_option autoImplicit true
open DeletionCode DeletionCode.SpectrumPrefixChange
open Windows CatalogueWords SignedSupport SpectrumLocalization

theorem DeletionCode.SpectrumPrefixChange.prefix_change (pre p q : List Bool) (L : ℕ) (hL : 1 ≤ L)
    (hp : L ≤ p.length + 1) (hq : L ≤ q.length + 1)
    (hprefix : Agree (listLetters p) 0 (listLetters q) 0 (L - 1)) (g : Gram L) :
    spectrum (pre ++ q) L g - spectrum (pre ++ p) L g =
      spectrum q L g - spectrum p L g := by sorry
