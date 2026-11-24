-- Prove2me | Theorems.Thm_FongoSync_keep_swap
-- name    : FongoSync.keep_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:01.105888+00:00
-- url     : https://prove2.me/theorems/59178556-ba77-439c-8297-d3ae6a6ffbff
-- title:
--   Fongo Sync: keep swap
-- statement:
--   Two entries may arrive in either order, provided equal keys mean equal entries.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L63-L93
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L63-L93

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

theorem FongoSync.keep_swap (h : Option E) (a b : E) (inj : key a = key b → a = b) :
    keep cmp key (keep cmp key h a) b = keep cmp key (keep cmp key h b) a := by sorry
