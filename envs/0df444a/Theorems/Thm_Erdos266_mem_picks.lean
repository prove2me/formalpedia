-- Prove2me | Theorems.Thm_Erdos266_mem_picks
-- name    : Erdos266.mem_picks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:01.531407+00:00
-- url     : https://prove2.me/theorems/7688c95a-2853-44a0-8dbf-460fccfbb20c
-- title:
--   Erdos266: mem picks
-- statement:
--   The Erdos266 construction uses the mem picks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L74-L86
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L74-L86

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.mem_picks {q : ℚ} {i : ℕ} : q ∈ picks i ↔ ∃ j < i, tSeq j = q := by sorry
