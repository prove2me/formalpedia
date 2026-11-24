-- Prove2me | Theorems.Thm_FongoSync_exists_stable
-- name    : FongoSync.exists_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:39.572179+00:00
-- url     : https://prove2.me/theorems/144c3057-067f-4c98-8f4c-f37e6d90226a
-- title:
--   Fongo Sync: exists stable
-- statement:
--   Some round up to the number of gids is stable.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L120-L135
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L120-L135

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.exists_stable : ∃ k ≤ inp.gids.length,
    ∀ g ∈ inp.gids, liveAt sc inp (k + 1) g → liveAt sc inp k g := by sorry
