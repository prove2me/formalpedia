-- Prove2me | Theorems.Thm_FongoSync_canonical_eq_iff
-- name    : FongoSync.canonical_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:45.737006+00:00
-- url     : https://prove2.me/theorems/87380934-4dac-4463-897a-ff9c0e62a459
-- title:
--   Fongo Sync: canonical eq iff
-- statement:
--   Two gids are in one group exactly when they have the same canonical gid.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L138-L140
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L138-L140

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.canonical_eq_iff (E : List Edge) (a b : Gid) :
    canonical E a = canonical E b ↔ Connected E a b := by sorry
