-- Prove2me | Theorems.Thm_FongoSync_Clock_tick_node
-- name    : FongoSync.Clock.tick_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:06.407633+00:00
-- url     : https://prove2.me/theorems/ccf4f877-d904-4a6b-9e38-0f78a9cc784a
-- title:
--   Clock: tick node
-- statement:
--   A tick keeps the node's own id.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L129-L132
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Clock.lean#L129-L132

import Definitions.Def_FongoSync_Clock
set_option autoImplicit false
open FongoSync

theorem FongoSync.Clock.tick_node (c : Clock) (wall : Nat) : (c.tick wall).1.node = c.last.node := by sorry
