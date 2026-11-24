-- Prove2me | Theorems.Thm_FongoSync_gidSet_eq_of_mem_iff
-- name    : FongoSync.gidSet_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:00.114557+00:00
-- url     : https://prove2.me/theorems/02706543-81d5-4aa0-a2e3-05152ffecae4
-- title:
--   Fongo Sync: gid Set eq of mem iff
-- statement:
--   The Fongo Sync construction uses the gid Set eq of mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L100-L102
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L100-L102

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
set_option autoImplicit false
open FongoSync

theorem FongoSync.gidSet_eq_of_mem_iff {l₁ l₂ : List Gid} (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂) :
    gidSet l₁ = gidSet l₂ := by sorry
