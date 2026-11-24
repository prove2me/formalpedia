-- Prove2me | Theorems.Thm_FongoSync_Laws_lww_keeps_later_clock
-- name    : FongoSync.Laws.lww_keeps_later_clock
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:02.787735+00:00
-- url     : https://prove2.me/theorems/9383b8cc-37f3-435d-b7d2-c7b210cc64c0
-- title:
--   Laws: lww keeps later clock
-- statement:
--   Under `Lww` a register ends at the later of the two clocks.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L64-L67
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L64-L67

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.lww_keeps_later_clock (held e : Entry V) :
    (apply .lww (some held) e).map (·.clock) =
      some (if held.clock < e.clock then e.clock else held.clock) := by sorry
