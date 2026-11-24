-- Prove2me | Theorems.Thm_FongoSync_isCanonical_of_mem_iff
-- name    : FongoSync.isCanonical_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:46.93272+00:00
-- url     : https://prove2.me/theorems/bd77e54b-b246-4150-ba4c-20fb3af6336c
-- title:
--   Fongo Sync: is Canonical of mem iff
-- statement:
--   The Fongo Sync construction uses the is Canonical of mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L142-L145
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L142-L145

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.isCanonical_of_mem_iff {E₁ E₂ : List Edge} (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) {g r : Gid}
    (h : IsCanonical E₁ g r) : IsCanonical E₂ g r := by sorry
