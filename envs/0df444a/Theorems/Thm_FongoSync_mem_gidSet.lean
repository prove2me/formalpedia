-- Prove2me | Theorems.Thm_FongoSync_mem_gidSet
-- name    : FongoSync.mem_gidSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:01.816086+00:00
-- url     : https://prove2.me/theorems/0ab1f605-d3cc-420b-96d6-d2bd5e29ff8d
-- title:
--   Fongo Sync: mem gid Set
-- statement:
--   The Fongo Sync construction uses the mem gid Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L55-L60
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L55-L60

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
set_option autoImplicit false
open FongoSync

theorem FongoSync.mem_gidSet {x : Gid} {l : List Gid} : x ∈ gidSet l ↔ x ∈ l := by sorry
