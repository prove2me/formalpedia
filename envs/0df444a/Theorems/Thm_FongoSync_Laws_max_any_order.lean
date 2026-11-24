-- Prove2me | Theorems.Thm_FongoSync_Laws_max_any_order
-- name    : FongoSync.Laws.max_any_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:16.413727+00:00
-- url     : https://prove2.me/theorems/12e7c0fe-e06c-4c78-bbdf-c3d1b0bef8b6
-- title:
--   Laws: max any order
-- statement:
--   Under `Max`, two changes may arrive in either order, with no condition.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L81-L83
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L81-L83

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.max_any_order (h : Option (Entry V)) (a b : Entry V) :
    apply .max (apply .max h a) b = apply .max (apply .max h b) a := by sorry
