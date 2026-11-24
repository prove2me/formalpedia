-- Prove2me | Theorems.Thm_FongoSync_Full_inputs_eq
-- name    : FongoSync.Full.inputs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:05:42.563054+00:00
-- url     : https://prove2.me/theorems/5de42692-1c4e-4fad-a9a7-3c659133e4a2
-- title:
--   Full: inputs eq
-- statement:
--   The Full construction uses the inputs eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L405-L407
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L405-L407

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_inputs_eq

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.inputs_eq (unique : ClockDetermines cs₁) : inputs sc cs₁ = inputs sc cs₂ := by sorry
