-- Prove2me | Theorems.Thm_FongoSync_Full_mem_claimed_iff
-- name    : FongoSync.Full.mem_claimed_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:01.276119+00:00
-- url     : https://prove2.me/theorems/4fadf442-1fa8-444c-95c6-598ad8a02ddd
-- title:
--   Full: mem claimed iff
-- statement:
--   The Full construction uses the mem claimed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L342-L343
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L342-L343

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.mem_claimed_iff (c : Change Value) : c ∈ claimed sc cs₁ ↔ c ∈ claimed sc cs₂ := by sorry
