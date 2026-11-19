-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_seedKnown_mono
-- name    : DeletionCode.SelectedWindows.seedKnown_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:32.044762+00:00
-- url     : https://prove2.me/theorems/01fcee4f-6382-4f52-b2bd-1911ef30d778
-- title:
--   Selected Windows: seed Known mono
-- statement:
--   The Selected Windows construction uses the seed Known mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L56-L61
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L56-L61

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.seedKnown_mono (s t : Memory) (start L k : ℕ)
    (hext : Extends s t) (h : SeedKnown s start L k) :
    SeedKnown t start L k := by sorry
