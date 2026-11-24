-- Prove2me | Theorems.Thm_FongoSync_apply_any_order
-- name    : FongoSync.apply_any_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:02.089296+00:00
-- url     : https://prove2.me/theorems/b3a0d021-8b85-408e-bc00-1f58891464f6
-- title:
--   Fongo Sync: apply any order
-- statement:
--   Two changes to one field may arrive in either order. `Max` needs nothing; `Lww` needs the
--   two clocks to differ unless the changes are the same.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L351-L356
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L351-L356

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]
variable [TransOrd V] [LawfulEqOrd V]

theorem FongoSync.apply_any_order (s : Strategy) (h : Option (Entry V)) (a b : Entry V)
    (unique : a.clock = b.clock → a = b) :
    apply s (apply s h a) b = apply s (apply s h b) a := by sorry
