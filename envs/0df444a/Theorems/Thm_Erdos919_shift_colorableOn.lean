-- Prove2me | Theorems.Thm_Erdos919_shift_colorableOn
-- name    : Erdos919.shift_colorableOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:07.681163+00:00
-- url     : https://prove2.me/theorems/24891c9f-3bf8-415c-a58c-90fa84b87e14
-- title:
--   Erdos919: shift colorable On
-- statement:
--   The Erdos919 construction uses the shift colorable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L273-L287
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L273-L287

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

theorem Erdos919.shift_colorableOn {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    (S : Set I) (f : I → T → Bool) (hf : Set.InjOn f S) :
    ColorableOn (shift I) {p | p.1.1 ∈ S ∧ p.1.2 ∈ S} (T × Bool) := by sorry
