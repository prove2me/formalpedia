-- Prove2me | Theorems.Thm_Erdos919_aleph1_lt_aleph2
-- name    : Erdos919.aleph1_lt_aleph2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:25.074724+00:00
-- url     : https://prove2.me/theorems/0a23abd5-3b3e-45ec-aaf6-6a8e53237d5b
-- title:
--   Erdos919: aleph1 lt aleph2
-- statement:
--   The Erdos919 construction uses the aleph1 lt aleph2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L345-L346
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L345-L346

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

theorem Erdos919.aleph1_lt_aleph2 : (ℵ₁ : Cardinal.{u}) < ℵ_ 2 := by sorry
