-- Prove2me | Theorems.Thm_Erdos266_tSeq_not_mem_picks
-- name    : Erdos266.tSeq_not_mem_picks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:09.384804+00:00
-- url     : https://prove2.me/theorems/f6623c45-8adc-43db-9151-62c9c9855ddf
-- title:
--   Erdos266: t Seq not mem picks
-- statement:
--   The Erdos266 construction uses the t Seq not mem picks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L67-L68
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L67-L68

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.tSeq_not_mem_picks (i : ℕ) : tSeq i ∉ picks i := by sorry
