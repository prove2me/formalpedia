-- Prove2me | Theorems.Thm_Erdos919_diffColor_ne
-- name    : Erdos919.diffColor_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:01.290367+00:00
-- url     : https://prove2.me/theorems/d35e2505-18d8-4e52-8b72-7cfb12f92f7d
-- title:
--   Erdos919: diff Color ne
-- statement:
--   The Erdos919 construction uses the diff Color ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L261-L271
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L261-L271

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

theorem Erdos919.diffColor_ne {T : Type*} [LinearOrder T] [WellFoundedLT T] [Inhabited T]
    {x y z : T → Bool} (hxy : x ≠ y) (hyz : y ≠ z) : diffColor x y ≠ diffColor y z := by sorry
