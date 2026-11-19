-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_mono
-- name    : DeletionCode.SelectedWindows.windowKnown_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:01:13.453479+00:00
-- url     : https://prove2.me/theorems/1089fe4a-e8cc-405a-93b9-520ae05fff2c
-- title:
--   Selected Windows: window Known mono
-- statement:
--   The Selected Windows construction uses the window Known mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L48-L54
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L48-L54

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.windowKnown_mono (s t : Memory) (start len : ℕ)
    (hext : Extends s t) (h : WindowKnown s start len) :
    WindowKnown t start len := by sorry
