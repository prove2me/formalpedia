-- Prove2me | Theorems.Thm_FongoSync_view_eq_of_mem_iff
-- name    : FongoSync.view_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:42.331683+00:00
-- url     : https://prove2.me/theorems/09c2534b-7132-42df-8f41-725430874e81
-- title:
--   Fongo Sync: view eq of mem iff
-- statement:
--   **The view is a function of the set of changes.** Two replicas that have seen the same set of
--   changes show the same data, whatever order the changes arrived in and however often.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L330-L339
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/View.lean#L330-L339

import Definitions.Def_FongoSync_State
import Definitions.Def_FongoSync_Alias
import Definitions.Def_FongoSync_GidSet
import Definitions.Def_FongoSync_View
import Theorems.Thm_FongoSync_IsCanonical_unique

set_option autoImplicit false
open FongoSync
open Std Classical
set_option linter.unusedSectionVars false

theorem FongoSync.view_eq_of_mem_iff (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    view sc cs₁ = view sc cs₂ := by sorry
