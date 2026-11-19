-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_windowKnown_subblock
-- name    : DeletionCode.SelectedWindows.windowKnown_subblock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:26.035453+00:00
-- url     : https://prove2.me/theorems/90ee7f32-2faf-415d-bfd9-9e19774cb1c2
-- title:
--   Selected Windows: window Known subblock
-- statement:
--   Every subblock of a readable block can itself be read.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L39-L46
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L39-L46

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.windowKnown_subblock (s : Memory) (a m b len : ℕ)
    (h : WindowKnown s a m) (hab : a ≤ b) (hbound : b + len ≤ a + m) :
    WindowKnown s b len := by sorry
