-- Prove2me | Theorems.Thm_FongoSync_Full_groupedAt_eq
-- name    : FongoSync.Full.groupedAt_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:13.602798+00:00
-- url     : https://prove2.me/theorems/656dda6a-5e10-49b3-befe-0f083da333bd
-- title:
--   Full: grouped At eq
-- statement:
--   The Full construction uses the grouped At eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L384-L398
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L384-L398

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.groupedAt_eq (unique : ClockDetermines cs₁) (k : Nat) :
    groupedAt sc cs₁ k = groupedAt sc cs₂ k := by sorry
