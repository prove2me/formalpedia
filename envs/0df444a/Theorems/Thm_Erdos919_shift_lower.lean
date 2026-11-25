-- Prove2me | Theorems.Thm_Erdos919_shift_lower
-- name    : Erdos919.shift_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:31:44.368472+00:00
-- url     : https://prove2.me/theorems/531f0ba9-133f-5901-9c4f-2adda30c541d
-- title:
--   Erdos919: shift lower
-- statement:
--   The Erdos919 construction uses the shift lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L235-L250
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L235-L250

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

theorem Erdos919.shift_lower {α : Type*} (c : (shift I).Coloring α) : Function.Injective
    (fun b : I => {a : α | ∃ g : I, ∃ h : b < g, c ⟨(b, g), h⟩ = a}) := by sorry
