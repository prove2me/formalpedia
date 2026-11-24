-- Prove2me | Theorems.Thm_FongoSync_Full_registers_eq
-- name    : FongoSync.Full.registers_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:30.408656+00:00
-- url     : https://prove2.me/theorems/d94710ef-a34c-467b-b18d-b326a1a37ff5
-- title:
--   Full: registers eq
-- statement:
--   The Full construction uses the registers eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L374-L382
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L374-L382

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false
variable (sc : Full.Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
include same

theorem FongoSync.Full.registers_eq (unique : ClockDetermines cs₁) : registers sc cs₁ = registers sc cs₂ := by sorry
