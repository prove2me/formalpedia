-- Prove2me | Theorems.Thm_FongoSync_Laws_tick_later
-- name    : FongoSync.Laws.tick_later
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:18.115364+00:00
-- url     : https://prove2.me/theorems/829b5210-3831-4057-a788-b2ebf4f4ce95
-- title:
--   Laws: tick later
-- statement:
--   A tick's reading is later than the clock's last reading, whatever the wall says.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L22-L23
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L22-L23

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.tick_later (c : Clock) (wall : Nat) : c.last < (c.tick wall).1 := by sorry
