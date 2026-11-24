-- Prove2me | Theorems.Thm_FongoSync_merged_at
-- name    : FongoSync.merged_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:25.403168+00:00
-- url     : https://prove2.me/theorems/df9a2b58-a471-489d-829b-7cd93c9da8ad
-- title:
--   Fongo Sync: merged at
-- statement:
--   One register of the merged state is the fold of that register's changes.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L81-L83
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/State.lean#L81-L83

import Definitions.Def_FongoSync_Register
import Definitions.Def_FongoSync_State
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {V : Type}
variable [Ord V]

theorem FongoSync.merged_at (σ : String → String → Strategy) (cs : List (Change V)) (k : Key) :
    merged σ cs k = (entriesAt cs k).foldl (apply (strategyAt σ k)) none := by sorry
