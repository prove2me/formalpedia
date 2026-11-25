-- Prove2me | Theorems.Thm_Erdos919_shift_adj
-- name    : Erdos919.shift_adj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:18:57.665024+00:00
-- url     : https://prove2.me/theorems/6449017e-306f-5b72-89ee-914c4eaf1a55
-- title:
--   Erdos919: shift adj
-- statement:
--   The Erdos919 construction uses the shift adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L232-L233
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L232-L233

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
variable (I : Type*) [LinearOrder I]
variable {I}

theorem Erdos919.shift_adj {p q : {p : I × I // p.1 < p.2}} :
    (shift I).Adj p q ↔ (p.1.2 = q.1.1 ∨ q.1.2 = p.1.1) := by sorry
