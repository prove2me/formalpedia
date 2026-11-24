-- Prove2me | Theorems.Thm_FongoSync_Clock_observe_notAfter
-- name    : FongoSync.Clock.observe_notAfter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:57:16.979195+00:00
-- url     : https://prove2.me/theorems/3f688abd-a359-4982-98c1-83bcc3368a40
-- title:
--   Clock: observe not After
-- statement:
--   Observing never moves the clock back, and leaves it at or past any encodable remote reading.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L140-L146
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L140-L146

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.observe_notAfter (c : Clock) (remote : Hlc) :
    c.last.NotAfter (c.observe remote).last ∧
      (remote.encodable → remote.NotAfter (c.observe remote).last) := by sorry
