-- Prove2me | Theorems.Thm_Erdos266_bigM_le_sqrt
-- name    : Erdos266.bigM_le_sqrt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:40:09.897297+00:00
-- url     : https://prove2.me/theorems/494c9dc6-3aac-59ff-b1f0-4a5f3309e6be
-- title:
--   Erdos266: big M le sqrt
-- statement:
--   The Erdos266 construction uses the big M le sqrt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L67-L67
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L67-L67

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.bigM_le_sqrt (k : ℕ) : bigM k ≤ Nat.sqrt (bigN k) := by sorry
