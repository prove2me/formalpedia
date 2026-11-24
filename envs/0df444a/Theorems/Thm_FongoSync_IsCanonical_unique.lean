-- Prove2me | Theorems.Thm_FongoSync_IsCanonical_unique
-- name    : FongoSync.IsCanonical.unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:53.392022+00:00
-- url     : https://prove2.me/theorems/a5f88696-cd6e-4e75-8f44-3c98d82c0769
-- title:
--   Is Canonical: unique
-- statement:
--   The Is Canonical construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L54-L56
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Alias.lean#L54-L56

import Definitions.Def_FongoSync_Clock
import Definitions.Def_FongoSync_Alias
set_option autoImplicit false
open FongoSync

theorem FongoSync.IsCanonical.unique {E : List Edge} {g r r' : Gid} (h : IsCanonical E g r)
    (h' : IsCanonical E g r') : r = r' := by sorry
