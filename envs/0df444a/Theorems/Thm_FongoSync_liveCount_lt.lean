-- Prove2me | Theorems.Thm_FongoSync_liveCount_lt
-- name    : FongoSync.liveCount_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:38.72864+00:00
-- url     : https://prove2.me/theorems/0a6a4b3c-88c9-46db-8af2-2a11c568aae6
-- title:
--   Fongo Sync: live Count lt
-- statement:
--   If round `k` is not stable, it adds a gid.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L111-L117
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L111-L117

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveCount_lt {k : Nat} (h : ¬ ∀ g ∈ inp.gids, liveAt sc inp (k + 1) g → liveAt sc inp k g) :
    liveCount sc inp k < liveCount sc inp (k + 1) := by sorry
