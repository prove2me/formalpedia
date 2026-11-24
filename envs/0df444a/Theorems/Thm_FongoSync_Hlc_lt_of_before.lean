-- Prove2me | Theorems.Thm_FongoSync_Hlc_lt_of_before
-- name    : FongoSync.Hlc.lt_of_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:11.559799+00:00
-- url     : https://prove2.me/theorems/7ef449f3-e89a-4035-8c6c-9691f383008d
-- title:
--   Hlc: lt of before
-- statement:
--   The Hlc construction uses the lt of before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L100-L101
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L100-L101

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Hlc.lt_of_before {a b : Hlc} (h : a.Before b) : a < b := by sorry
