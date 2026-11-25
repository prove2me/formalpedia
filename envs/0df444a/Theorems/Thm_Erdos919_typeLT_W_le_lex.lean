-- Prove2me | Theorems.Thm_Erdos919_typeLT_W_le_lex
-- name    : Erdos919.typeLT_W_le_lex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:21.650341+00:00
-- url     : https://prove2.me/theorems/49384620-ddfc-5d12-bec6-47dc8c28d859
-- title:
--   Erdos919: type LT W le lex
-- statement:
--   The Erdos919 construction uses the type LT W le lex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L467-L469
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L467-L469

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section

theorem Erdos919.typeLT_W_le_lex : typeLT W.{u} ≤ typeLT (W.{u} ×ₗ W.{u}) := by sorry
