-- Prove2me | Theorems.Thm_Erdos919_le_aleph1_of_lt_aleph2
-- name    : Erdos919.le_aleph1_of_lt_aleph2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:19:41.284578+00:00
-- url     : https://prove2.me/theorems/4c74ba01-056e-4a7d-81a0-44fda7d1fb8a
-- title:
--   Erdos919: le aleph1 of lt aleph2
-- statement:
--   The Erdos919 construction uses the le aleph1 of lt aleph2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L348-L349
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L348-L349

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

theorem Erdos919.le_aleph1_of_lt_aleph2 {c : Cardinal.{u}} (h : c < ℵ_ 2) : c ≤ ℵ₁ := by sorry
