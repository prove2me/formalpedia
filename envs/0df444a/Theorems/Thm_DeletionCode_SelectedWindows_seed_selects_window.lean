-- Prove2me | Theorems.Thm_DeletionCode_SelectedWindows_seed_selects_window
-- name    : DeletionCode.SelectedWindows.seed_selects_window
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:19.320066+00:00
-- url     : https://prove2.me/theorems/67d8cdfe-0860-47d2-8cbb-1159fee04209
-- title:
--   Selected Windows: seed selects window
-- statement:
--   A newly available k-stretch can initialize a realizable selected seed slot.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L100-L106
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SelectedWindows.lean#L100-L106

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_Recovery
import Definitions.Def_DeletionCode_SelectedWindows
set_option autoImplicit true
open DeletionCode DeletionCode.SelectedWindows
open Windows PartialWords Recovery

theorem DeletionCode.SelectedWindows.seed_selects_window (s : Memory) (D k a : ℕ) (hD : D < 3 * (k + 1))
    (ha : a + k ≤ 3 * (k + 1) + D) (hknown : WindowKnown s a k) :
    ∃ w : Slot, SeedKnown s (windowStart D w) (3 * (k + 1)) k := by sorry
