-- Prove2me | Theorems.Thm_FongoSync_inputs_eq
-- name    : FongoSync.inputs_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:44.046441+00:00
-- url     : https://prove2.me/theorems/58767d02-ace8-49fe-893d-db943800d537
-- title:
--   Fongo Sync: inputs eq
-- statement:
--   Changes with the same members give the same inputs once their registers agree.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L273-L279
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L273-L279

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.inputs_eq (sc : Schema) {cs₁ cs₂ : List (Change Value)} (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂)
    (regs : registers sc cs₁ = registers sc cs₂) : inputs sc cs₁ = inputs sc cs₂ := by sorry
