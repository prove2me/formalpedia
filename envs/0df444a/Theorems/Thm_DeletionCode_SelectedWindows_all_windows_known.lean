-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_all_windows_known
-- name    : DeletionCode.SelectedWindows.all_windows_known
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:48.405303+00:00
-- url     : https://prove2.me/theorems/8bc23767-5e06-4973-8055-f3d9eab1c418
-- title:
--   Selected Windows: all windows known
-- statement:
--   The first and last selected windows already cover every letter of the path.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L109-L120
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L109-L120

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.all_windows_known (s : Memory) (D L : ℕ) (hD : D ≤ L)
    (hknown : ∀ w : Slot, WindowKnown s (windowStart D w) L) :
    WindowKnown s 0 (L + D) := by sorry
