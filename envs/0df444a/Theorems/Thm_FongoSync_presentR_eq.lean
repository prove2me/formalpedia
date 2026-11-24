-- Prove2me | Theorems.Thm_FongoSync_presentR_eq
-- name    : FongoSync.presentR_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:00.106623+00:00
-- url     : https://prove2.me/theorems/215321e8-735a-4c02-812f-aa111909d309
-- title:
--   Fongo Sync: present R eq
-- statement:
--   The Fongo Sync construction uses the present R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L249-L280
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Run.lean#L249-L280

import Definitions.Def_FongoSync_View
import Definitions.Def_FongoSync_Run
set_option autoImplicit false
open FongoSync
open Classical
variable (sc : Schema) (inp : Inputs)

theorem FongoSync.presentR_eq : presentR sc inp = present sc inp := by sorry
