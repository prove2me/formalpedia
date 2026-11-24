-- Prove2me | Theorems.Thm_FongoSync_Laws_apply_twice
-- name    : FongoSync.Laws.apply_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:07.677511+00:00
-- url     : https://prove2.me/theorems/4c13c08d-d53c-41d6-969c-96fb9d73fd1e
-- title:
--   Laws: apply twice
-- statement:
--   Receiving a change twice is receiving it once, under either strategy.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L70-L72
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L70-L72

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
import Theorems.Thm_FongoSync_State_apply_twice
import Theorems.Thm_FongoSync_apply_twice

set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync
variable {V : Type} [Ord V] [Std.TransOrd V] [Std.LawfulEqOrd V]

theorem FongoSync.Laws.apply_twice (s : Strategy) (h : Option (Entry V)) (e : Entry V) :
    apply s (apply s h e) e = apply s h e := by sorry
