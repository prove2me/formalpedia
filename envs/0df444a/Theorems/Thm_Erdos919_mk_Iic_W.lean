-- Prove2me | Theorems.Thm_Erdos919_mk_Iic_W
-- name    : Erdos919.mk_Iic_W
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:31.341271+00:00
-- url     : https://prove2.me/theorems/b69c7b2c-57f4-4d4c-b550-7cb5f89e45c3
-- title:
--   Erdos919: mk Iic W
-- statement:
--   The Erdos919 construction uses the mk Iic W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L354-L357
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L354-L357

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

theorem Erdos919.mk_Iic_W (x : W.{u}) : #(Iic x) ≤ ℵ₁ := by sorry
