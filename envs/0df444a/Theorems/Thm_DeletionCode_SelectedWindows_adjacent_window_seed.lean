-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_adjacent_window_seed
-- name    : DeletionCode.SelectedWindows.adjacent_window_seed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:03:35.336628+00:00
-- url     : https://prove2.me/theorems/fe98394b-d9b6-4258-b2bc-5287d2d2ed43
-- title:
--   Selected Windows: adjacent window seed
-- statement:
--   An already read adjacent selected window supplies a readable k-seed.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L74-L84
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L74-L84

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.adjacent_window_seed (s : Memory) (D k : ℕ) (v w : Slot)
    (hD : D < 3 * (k + 1)) (hadj : AdjSlot v w)
    (hknown : WindowKnown s (windowStart D v) (3 * (k + 1))) :
    SeedKnown s (windowStart D w) (3 * (k + 1)) k := by sorry
