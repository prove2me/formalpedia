-- Prove2me | Theorems.Thm_Erdos266_bigN_succ
-- name    : Erdos266.bigN_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:48.606251+00:00
-- url     : https://prove2.me/theorems/780abf33-286d-4f6a-a006-8f216beff744
-- title:
--   Erdos266: big N succ
-- statement:
--   The Erdos266 construction uses the big N succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L47-L50
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L47-L50

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.bigN_succ (k : ℕ) : bigN (k + 1) = 2 ^ (2 * k + 1) * bigN k := by sorry
