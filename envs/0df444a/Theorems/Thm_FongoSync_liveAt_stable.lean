-- Prove2me | Theorems.Thm_FongoSync_liveAt_stable
-- name    : FongoSync.liveAt_stable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:34.377951+00:00
-- url     : https://prove2.me/theorems/fe165c72-8a83-4406-abd3-5e230e9d9203
-- title:
--   Fongo Sync: live At stable
-- statement:
--   Once a round adds nothing, no later round does.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L64-L76
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L64-L76

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveAt_stable {k : Nat} (hs : ∀ g ∈ inp.gids, liveAt sc inp (k + 1) g → liveAt sc inp k g)
    (j : Nat) (g : Gid) : liveAt sc inp (k + j) g ↔ liveAt sc inp k g := by sorry
