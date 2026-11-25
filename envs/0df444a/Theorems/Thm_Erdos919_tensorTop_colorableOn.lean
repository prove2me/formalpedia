-- Prove2me | Theorems.Thm_Erdos919_tensorTop_colorableOn
-- name    : Erdos919.tensorTop_colorableOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:31:54.130665+00:00
-- url     : https://prove2.me/theorems/45d740ea-5e18-4964-8a5a-f2c07733a507
-- title:
--   Erdos919: tensor Top colorable On
-- statement:
--   The Erdos919 construction uses the tensor Top colorable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L211-L214
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L211-L214

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

theorem Erdos919.tensorTop_colorableOn {V T α : Type*} (H : SimpleGraph V) (X : Set (V × T))
    (h : ColorableOn H (Prod.fst '' X) α) : ColorableOn (tensorTop H T) X α := by sorry
