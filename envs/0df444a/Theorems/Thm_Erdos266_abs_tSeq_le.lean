-- Prove2me | Theorems.Thm_Erdos266_abs_tSeq_le
-- name    : Erdos266.abs_tSeq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:08.03323+00:00
-- url     : https://prove2.me/theorems/87843f5c-dd3c-4796-8c48-4fc7e96df9b8
-- title:
--   Erdos266: abs t Seq le
-- statement:
--   The growth condition (7.1).
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L71-L72
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L71-L72

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.abs_tSeq_le (i : ℕ) : |tSeq i| ≤ (i : ℚ) + 1 := by sorry
