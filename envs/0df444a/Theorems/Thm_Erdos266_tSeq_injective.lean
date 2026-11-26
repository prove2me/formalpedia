-- Prove2me | Theorems.Thm_Erdos266_tSeq_injective
-- name    : Erdos266.tSeq_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:00.253998+00:00
-- url     : https://prove2.me/theorems/3b6592e6-e396-5e45-8822-500ddfdb8c48
-- title:
--   Erdos266: t Seq injective
-- statement:
--   The Erdos266 construction uses the t Seq injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L88-L93
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Enumeration.lean#L88-L93

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
set_option autoImplicit false
@[expose] public section
public section
open Erdos266

theorem Erdos266.tSeq_injective : Function.Injective tSeq := by sorry
