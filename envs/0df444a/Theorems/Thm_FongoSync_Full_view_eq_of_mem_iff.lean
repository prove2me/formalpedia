-- Prove2me | Theorems.Thm_FongoSync_Full_view_eq_of_mem_iff
-- name    : FongoSync.Full.view_eq_of_mem_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:05.287549+00:00
-- url     : https://prove2.me/theorems/93c15bcd-9cfa-49d1-936e-be468a82d6c2
-- title:
--   Full: view eq of mem iff
-- statement:
--   **The view over several collections depends only on the set of changes**, given that no two
--   changes to one register share a clock with different values.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L413-L419
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Model.lean#L413-L419

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Model
import Theorems.Thm_FongoSync_IsCanonical_unique
import Theorems.Thm_FongoSync_view_eq_of_mem_iff

set_option autoImplicit false
open FongoSync FongoSync.Full
open Std Classical FongoSync
set_option linter.unusedSectionVars false

theorem FongoSync.Full.view_eq_of_mem_iff (sc : Schema) {cs₁ cs₂ : List (Change Value)}
    (same : ∀ c, c ∈ cs₁ ↔ c ∈ cs₂) (unique : ClockDetermines cs₁) :
    view sc cs₁ = view sc cs₂ := by sorry
