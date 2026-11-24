-- Prove2me | Theorems.Thm_FongoSync_canonical_perm
-- name    : FongoSync.canonical_perm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:46.724936+00:00
-- url     : https://prove2.me/theorems/4d02f506-aa6f-4585-80f3-f7ff5412691e
-- title:
--   Fongo Sync: canonical perm
-- statement:
--   The Fongo Sync construction uses the canonical perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L158-L159
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L158-L159

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.canonical_perm {E₁ E₂ : List Edge} (p : E₁.Perm E₂) : canonical E₁ = canonical E₂ := by sorry
