-- Prove2me | Theorems.Thm_Erdos266_one_le_bigN
-- name    : Erdos266.one_le_bigN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:39:25.987926+00:00
-- url     : https://prove2.me/theorems/199549f7-b0b3-5139-8e79-8e4e732fbfe6
-- title:
--   Erdos266: one le big N
-- statement:
--   The Erdos266 construction uses the one le big N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L43-L43
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L43-L43

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.one_le_bigN (k : ℕ) : 1 ≤ bigN k := by sorry
