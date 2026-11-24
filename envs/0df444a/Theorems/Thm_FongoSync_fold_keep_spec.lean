-- Prove2me | Theorems.Thm_FongoSync_fold_keep_spec
-- name    : FongoSync.fold_keep_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:08.732679+00:00
-- url     : https://prove2.me/theorems/3fd95f69-894a-4748-a150-ed415f57f816
-- title:
--   Fongo Sync: fold keep spec
-- statement:
--   Folding `keep` from `h` over `l` ends at an entry of `h` or `l` whose key is at least that of
--   every entry seen.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L157-L201
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L157-L201

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

theorem FongoSync.fold_keep_spec (l : List E) (h : Option E) (m : E)
    (hm : l.foldl (keep cmp key) h = some m) :
    (h = some m ∨ m ∈ l) ∧ (∀ x ∈ l, (cmp (key x) (key m)).isLE) ∧
      (∀ s, h = some s → (cmp (key s) (key m)).isLE) := by sorry
