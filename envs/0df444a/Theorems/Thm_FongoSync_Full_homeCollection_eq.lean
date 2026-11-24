-- Prove2me | Theorems.Thm_FongoSync_Full_homeCollection_eq
-- name    : FongoSync.Full.homeCollection_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:04.229154+00:00
-- url     : https://prove2.me/theorems/f5a3b4f9-462a-4964-abf6-7a43beca170a
-- title:
--   Full: home Collection eq
-- statement:
--   The Full construction uses the home Collection eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L348-L349
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L348-L349

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.homeCollection_eq : homeCollection sc cs₁ = homeCollection sc cs₂ := by sorry
