-- Prove2me | Theorems.Thm_Erdos919_mk_ulift_nat_le_aleph1
-- name    : Erdos919.mk_ulift_nat_le_aleph1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:29.156485+00:00
-- url     : https://prove2.me/theorems/b409e1e1-b67b-449c-b103-c21900be9f76
-- title:
--   Erdos919: mk ulift nat le aleph1
-- statement:
--   The Erdos919 construction uses the mk ulift nat le aleph1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L359-L360
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L359-L360

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

theorem Erdos919.mk_ulift_nat_le_aleph1 : #(ULift.{u} ℕ) ≤ ℵ₁ := by sorry
