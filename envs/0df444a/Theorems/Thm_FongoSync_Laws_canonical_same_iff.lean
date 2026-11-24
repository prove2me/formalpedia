-- Prove2me | Theorems.Thm_FongoSync_Laws_canonical_same_iff
-- name    : FongoSync.Laws.canonical_same_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:40.329762+00:00
-- url     : https://prove2.me/theorems/cf759347-30c6-4234-a43d-de013b87191e
-- title:
--   Laws: canonical same iff
-- statement:
--   Two gids share a canonical gid exactly when aliases connect them.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L132-L134
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L132-L134

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.canonical_same_iff (E : List Edge) (a b : Gid) :
    canonical E a = canonical E b ↔ Connected E a b := by sorry
