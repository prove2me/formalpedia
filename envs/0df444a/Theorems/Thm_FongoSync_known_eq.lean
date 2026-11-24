-- Prove2me | Theorems.Thm_FongoSync_known_eq
-- name    : FongoSync.known_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:02.039142+00:00
-- url     : https://prove2.me/theorems/6b4c31cc-1800-404d-bee1-c02b0f5e580e
-- title:
--   Fongo Sync: known eq
-- statement:
--   The Fongo Sync construction uses the known eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L268-L270
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L268-L270

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.known_eq (sc : Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) :
    known sc cs₁ = known sc cs₂ := by sorry
