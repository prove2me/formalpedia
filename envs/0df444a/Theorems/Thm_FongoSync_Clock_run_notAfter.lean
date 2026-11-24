-- Prove2me | Theorems.Thm_FongoSync_Clock_run_notAfter
-- name    : FongoSync.Clock.run_notAfter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:59:55.270882+00:00
-- url     : https://prove2.me/theorems/9a128dc5-b7f6-4281-bfc4-de547e0dc1ce
-- title:
--   Clock: run not After
-- statement:
--   The Clock construction uses the run not After property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L171-L200
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L171-L200

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.run_notAfter (c : Clock) (events : List Event) :
    c.last.NotAfter (c.run events).1.last ∧ ∀ r ∈ (c.run events).2, r.NotAfter (c.run events).1.last := by sorry
