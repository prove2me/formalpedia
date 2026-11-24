-- Prove2me | Theorems.Thm_FongoSync_Laws_groups_swap
-- name    : FongoSync.Laws.groups_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:42.170434+00:00
-- url     : https://prove2.me/theorems/19127a6a-328c-407c-a11b-56857b8284a9
-- title:
--   Laws: groups swap
-- statement:
--   Swapping two neighbouring aliases anywhere leaves every canonical gid the same.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L137-L139
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L137-L139

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.groups_swap (pre post : List Edge) (x y : Edge) :
    canonical (pre ++ x :: y :: post) = canonical (pre ++ y :: x :: post) := by sorry
