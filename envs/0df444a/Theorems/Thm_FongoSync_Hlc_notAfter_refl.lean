-- Prove2me | Theorems.Thm_FongoSync_Hlc_notAfter_refl
-- name    : FongoSync.Hlc.notAfter_refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:20.67334+00:00
-- url     : https://prove2.me/theorems/f7142d61-866b-4e0e-9cc6-93391c4851ce
-- title:
--   Hlc: not After refl
-- statement:
--   The Hlc construction uses the not After refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L111-L112
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L111-L112

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Hlc.notAfter_refl (a : Hlc) : a.NotAfter a := by sorry
