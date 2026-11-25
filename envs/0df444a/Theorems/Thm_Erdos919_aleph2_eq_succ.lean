-- Prove2me | Theorems.Thm_Erdos919_aleph2_eq_succ
-- name    : Erdos919.aleph2_eq_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:11.391278+00:00
-- url     : https://prove2.me/theorems/6419580c-36c2-5ec2-9fe0-6b2f45016c5d
-- title:
--   Erdos919: aleph2 eq succ
-- statement:
--   The Erdos919 construction uses the aleph2 eq succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L342-L343
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L342-L343

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

theorem Erdos919.aleph2_eq_succ : (ℵ_ 2 : Cardinal.{u}) = Order.succ ℵ₁ := by sorry
