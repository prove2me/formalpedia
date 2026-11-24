-- Prove2me | Theorems.Thm_FongoSync_Full_home_eq
-- name    : FongoSync.Full.home_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:05.549017+00:00
-- url     : https://prove2.me/theorems/278d3768-0987-4952-b5db-f98926bf8a15
-- title:
--   Full: home eq
-- statement:
--   The Full construction uses the home eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L334-L340
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L334-L340

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.home_eq : home sc cs₁ = home sc cs₂ := by sorry
