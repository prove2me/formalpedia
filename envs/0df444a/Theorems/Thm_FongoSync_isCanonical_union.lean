-- Prove2me | Theorems.Thm_FongoSync_isCanonical_union
-- name    : FongoSync.isCanonical_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:00:40.329941+00:00
-- url     : https://prove2.me/theorems/6c4cdd17-8b01-4662-a7f9-744e65171c7f
-- title:
--   Fongo Sync: is Canonical union
-- statement:
--   Adding one edge keeps every label canonical.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L75-L119
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L75-L119

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync
variable {P : List Edge} {L : Gid → Gid} (inv : ∀ g, IsCanonical P g (L g))
include inv

theorem FongoSync.isCanonical_union (e : Edge) (g : Gid) :
    IsCanonical (P ++ [e]) g (union L e g) := by sorry
