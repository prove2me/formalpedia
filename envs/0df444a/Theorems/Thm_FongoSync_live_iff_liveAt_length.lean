-- Prove2me | Theorems.Thm_FongoSync_live_iff_liveAt_length
-- name    : FongoSync.live_iff_liveAt_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:01:43.615865+00:00
-- url     : https://prove2.me/theorems/a63a2abd-d4f6-4784-94da-5078948df264
-- title:
--   Fongo Sync: live iff live At length
-- statement:
--   Live is live after as many rounds as there are gids.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L138-L148
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L138-L148

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.live_iff_liveAt_length (g : Gid) : Live sc inp g ↔ liveAt sc inp inp.gids.length g := by sorry
