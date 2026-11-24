-- Prove2me | Theorems.Thm_FongoSync_Hlc_before_of_notAfter_of_before
-- name    : FongoSync.Hlc.before_of_notAfter_of_before
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:17.048805+00:00
-- url     : https://prove2.me/theorems/2bcd91af-1d44-4491-bed3-ae12fb39d0cb
-- title:
--   Hlc: before of not After of before
-- statement:
--   The Hlc construction uses the before of not After of before property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L103-L105
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L103-L105

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Hlc.before_of_notAfter_of_before {a b c : Hlc} (h₁ : a.NotAfter b) (h₂ : b.Before c) :
    a.Before c := by sorry
