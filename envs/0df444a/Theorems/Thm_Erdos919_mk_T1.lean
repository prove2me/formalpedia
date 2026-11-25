-- Prove2me | Theorems.Thm_Erdos919_mk_T1
-- name    : Erdos919.mk_T1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:24:05.11771+00:00
-- url     : https://prove2.me/theorems/07290919-c630-4ceb-9b24-f7ecadc9e076
-- title:
--   Erdos919: mk T1
-- statement:
--   The Erdos919 construction uses the mk T1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L554-L554
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L554-L554

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

theorem Erdos919.mk_T1 : #T1.{u} = ℵ₁ := by sorry
