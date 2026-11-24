-- Prove2me | Theorems.Thm_FongoSync_eq_of_sorted
-- name    : FongoSync.eq_of_sorted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:03.237341+00:00
-- url     : https://prove2.me/theorems/cd20c45a-c5bb-4817-97d6-b3261bb59045
-- title:
--   Fongo Sync: eq of sorted
-- statement:
--   Two strictly increasing lists with the same members are the same list.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L68-L98
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/GidSet.lean#L68-L98

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_GidSet
set_option autoImplicit false
open FongoSync

theorem FongoSync.eq_of_sorted {l₁ l₂ : List Gid} (s₁ : l₁.Pairwise (· < ·)) (s₂ : l₂.Pairwise (· < ·))
    (same : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by sorry
