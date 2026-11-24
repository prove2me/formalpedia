-- Prove2me | Theorems.Thm_FongoSync_mem_insertGid
-- name    : FongoSync.mem_insertGid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:45.574455+00:00
-- url     : https://prove2.me/theorems/75f5ef8d-4acc-4bf7-8741-1a40bf9eca0b
-- title:
--   Fongo Sync: mem insert Gid
-- statement:
--   The Fongo Sync construction uses the mem insert Gid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L20-L32
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L20-L32

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
set_option autoImplicit false
open FongoSync

theorem FongoSync.mem_insertGid {g x : Gid} {l : List Gid} : x ∈ insertGid g l ↔ x = g ∨ x ∈ l := by sorry
