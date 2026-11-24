-- Prove2me | Theorems.Thm_FongoSync_Full_mem_edges_iff
-- name    : FongoSync.Full.mem_edges_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:16.838155+00:00
-- url     : https://prove2.me/theorems/38633f00-70c1-4568-bf87-bbe242ce0e17
-- title:
--   Full: mem edges iff
-- statement:
--   The Full construction uses the mem edges iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L369-L372
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L369-L372

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.mem_edges_iff (e : Edge) : e ∈ edges sc cs₁ ↔ e ∈ edges sc cs₂ := by sorry
