-- Prove2me | Theorems.Thm_Erdos266_one_le_bigM
-- name    : Erdos266.one_le_bigM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:40:17.562163+00:00
-- url     : https://prove2.me/theorems/b06b7e4d-8da8-5d2d-8c68-547e363641f8
-- title:
--   Erdos266: one le big M
-- statement:
--   The Erdos266 construction uses the one le big M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L72-L87
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L72-L87

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.one_le_bigM {k : ℕ} (hk : 2 ≤ k) : 1 ≤ bigM k := by sorry
