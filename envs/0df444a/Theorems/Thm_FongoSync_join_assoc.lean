-- Prove2me | Theorems.Thm_FongoSync_join_assoc
-- name    : FongoSync.join_assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:15.184609+00:00
-- url     : https://prove2.me/theorems/d062e292-7321-4c2f-b658-73c5242c702b
-- title:
--   Fongo Sync: join assoc
-- statement:
--   Associativity needs no hypothesis: on equal keys the left operand is kept throughout.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L131-L153
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L131-L153

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}

theorem FongoSync.join_assoc (a b c : Option E) :
    join cmp key (join cmp key a b) c = join cmp key a (join cmp key b c) := by sorry
