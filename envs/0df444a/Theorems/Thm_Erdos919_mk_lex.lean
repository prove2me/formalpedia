-- Prove2me | Theorems.Thm_Erdos919_mk_lex
-- name    : Erdos919.mk_lex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:43.384841+00:00
-- url     : https://prove2.me/theorems/d30e62b3-cf01-4546-9461-1a1bd8472132
-- title:
--   Erdos919: mk lex
-- statement:
--   The Erdos919 construction uses the mk lex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L476-L478
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L476-L478

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

theorem Erdos919.mk_lex : #(W.{u} ×ₗ W.{u}) = ℵ_ 2 := by sorry
