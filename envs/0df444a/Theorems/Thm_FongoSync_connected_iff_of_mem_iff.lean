-- Prove2me | Theorems.Thm_FongoSync_connected_iff_of_mem_iff
-- name    : FongoSync.connected_iff_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:03:21.260766+00:00
-- url     : https://prove2.me/theorems/de997a08-038a-46b2-a7cb-a05f4e2acece
-- title:
--   Fongo Sync: connected iff of mem iff
-- statement:
--   The Fongo Sync construction uses the connected iff of mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L154-L156
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L154-L156

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.connected_iff_of_mem_iff {E₁ E₂ : List Edge} (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) (a b : Gid) :
    Connected E₁ a b ↔ Connected E₂ a b := by sorry
