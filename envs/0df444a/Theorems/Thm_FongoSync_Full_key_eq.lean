-- Prove2me | Theorems.Thm_FongoSync_Full_key_eq
-- name    : FongoSync.Full.key_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:35.673095+00:00
-- url     : https://prove2.me/theorems/b04c2e1a-b789-40be-a8db-ce2cff827716
-- title:
--   Full: key eq
-- statement:
--   The Full construction uses the key eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L355-L358
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L355-L358

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.key_eq : key sc cs₁ = key sc cs₂ := by sorry
