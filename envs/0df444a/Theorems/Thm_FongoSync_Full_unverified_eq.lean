-- Prove2me | Theorems.Thm_FongoSync_Full_unverified_eq
-- name    : FongoSync.Full.unverified_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:00.913144+00:00
-- url     : https://prove2.me/theorems/efdc3802-dbaa-4200-b686-e84c410feae5
-- title:
--   Full: unverified eq
-- statement:
--   The Full construction uses the unverified eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L360-L362
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L360-L362

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.unverified_eq : Unverified sc cs₁ = Unverified sc cs₂ := by sorry
