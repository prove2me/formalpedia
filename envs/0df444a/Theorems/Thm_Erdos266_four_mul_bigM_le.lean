-- Prove2me | Theorems.Thm_Erdos266_four_mul_bigM_le
-- name    : Erdos266.four_mul_bigM_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:42:16.595672+00:00
-- url     : https://prove2.me/theorems/46600848-b172-5231-962c-0918ca1ea374
-- title:
--   Erdos266: four mul big M le
-- statement:
--   The Erdos266 construction uses the four mul big M le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L57-L60
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L57-L60

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.four_mul_bigM_le (k : ℕ) : 4 * k * bigM k ≤ bigN k := by sorry
