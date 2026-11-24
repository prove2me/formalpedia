-- Prove2me | Theorems.Thm_FongoSync_liveMembersR_eq
-- name    : FongoSync.liveMembersR_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:04.663483+00:00
-- url     : https://prove2.me/theorems/c0c3e847-9cea-44cb-9e29-420054717b00
-- title:
--   Fongo Sync: live Members R eq
-- statement:
--   The Fongo Sync construction uses the live Members R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L242-L247
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L242-L247

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.liveMembersR_eq (r : Gid) : liveMembersR sc inp r = liveMembers sc inp r := by sorry
