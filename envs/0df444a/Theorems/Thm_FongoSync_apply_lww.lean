-- Prove2me | Theorems.Thm_FongoSync_apply_lww
-- name    : FongoSync.apply_lww
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:53.114854+00:00
-- url     : https://prove2.me/theorems/049de5ad-5d47-406b-b93b-5a8366d87322
-- title:
--   Fongo Sync: apply lww
-- statement:
--   The Fongo Sync construction uses the apply lww property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L291-L298
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L291-L298

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type} [Ord V]

theorem FongoSync.apply_lww (held : Option (Entry V)) (e : Entry V) :
    apply .lww held e = keep compare Entry.clock held e := by sorry
