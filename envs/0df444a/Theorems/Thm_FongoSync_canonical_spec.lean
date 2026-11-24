-- Prove2me | Theorems.Thm_FongoSync_canonical_spec
-- name    : FongoSync.canonical_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:58:41.78866+00:00
-- url     : https://prove2.me/theorems/5c99ee75-0df2-41a7-9cf6-d246ab33baf0
-- title:
--   Fongo Sync: canonical spec
-- statement:
--   **`canonical` is right**: each gid's label is the smallest gid in its group.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L133-L135
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L133-L135

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.canonical_spec (E : List Edge) (g : Gid) : IsCanonical E g (canonical E g) := by sorry
