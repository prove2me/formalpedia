-- Prove2me | Theorems.Thm_FongoSync_Laws_groups_twice
-- name    : FongoSync.Laws.groups_twice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:54.131801+00:00
-- url     : https://prove2.me/theorems/5996f764-9728-446c-a368-45a351c1488a
-- title:
--   Laws: groups twice
-- statement:
--   An alias received twice in a row groups gids as receiving it once.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L142-L144
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L142-L144

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.groups_twice (pre post : List Edge) (x : Edge) :
    canonical (pre ++ x :: x :: post) = canonical (pre ++ x :: post) := by sorry
