-- Prove2me | Theorems.Thm_FongoSync_Full_gids_eq
-- name    : FongoSync.Full.gids_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:06.314058+00:00
-- url     : https://prove2.me/theorems/27fd228b-4c46-4718-b9d8-7942d26a432e
-- title:
--   Full: gids eq
-- statement:
--   The Full construction uses the gids eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L345-L346
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L345-L346

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.gids_eq : gids sc cs₁ = gids sc cs₂ := by sorry
