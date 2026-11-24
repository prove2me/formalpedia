-- Prove2me | Theorems.Thm_FongoSync_canonical_eq_of_mem_iff
-- name    : FongoSync.canonical_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:58.149411+00:00
-- url     : https://prove2.me/theorems/af9597f0-3164-445f-a222-ff9326ea25a8
-- title:
--   Fongo Sync: canonical eq of mem iff
-- statement:
--   **Alias groups converge.** The groups and canonical gids depend only on which edges were
--   seen: not their order, and not how often each arrived.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L149-L152
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L149-L152

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.canonical_eq_of_mem_iff (E₁ E₂ : List Edge) (same : ∀ e, e ∈ E₁ ↔ e ∈ E₂) :
    canonical E₁ = canonical E₂ := by sorry
