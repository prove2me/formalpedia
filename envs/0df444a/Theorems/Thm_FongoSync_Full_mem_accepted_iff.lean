-- Prove2me | Theorems.Thm_FongoSync_Full_mem_accepted_iff
-- name    : FongoSync.Full.mem_accepted_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:33.205996+00:00
-- url     : https://prove2.me/theorems/67a5d727-40c1-4dba-b640-aee961748c9b
-- title:
--   Full: mem accepted iff
-- statement:
--   The Full construction uses the mem accepted iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L364-L367
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L364-L367

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.mem_accepted_iff (c : Change Value) : c ∈ accepted sc cs₁ ↔ c ∈ accepted sc cs₂ := by sorry
