-- Prove2me | Theorems.Thm_FongoSync_mem_ours_iff
-- name    : FongoSync.mem_ours_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:33.789244+00:00
-- url     : https://prove2.me/theorems/b2575fa7-3a76-4aab-a5e0-45c520632ec5
-- title:
--   Fongo Sync: mem ours iff
-- statement:
--   The Fongo Sync construction uses the mem ours iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L264-L266
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L264-L266

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.mem_ours_iff (sc : Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
    (c : Change Value) : c ∈ ours sc cs₁ ↔ c ∈ ours sc cs₂ := by sorry
