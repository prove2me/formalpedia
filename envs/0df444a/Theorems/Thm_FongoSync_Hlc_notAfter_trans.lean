-- Prove2me | Theorems.Thm_FongoSync_Hlc_notAfter_trans
-- name    : FongoSync.Hlc.notAfter_trans
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:18.103238+00:00
-- url     : https://prove2.me/theorems/d23249a0-b3d2-4213-8dc4-d3d10ca61b6a
-- title:
--   Hlc: not After trans
-- statement:
--   The Hlc construction uses the not After trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L107-L109
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L107-L109

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Hlc.notAfter_trans {a b c : Hlc} (h₁ : a.NotAfter b) (h₂ : b.NotAfter c) :
    a.NotAfter c := by sorry
