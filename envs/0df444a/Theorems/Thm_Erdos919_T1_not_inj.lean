-- Prove2me | Theorems.Thm_Erdos919_T1_not_inj
-- name    : Erdos919.T1_not_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:31.69483+00:00
-- url     : https://prove2.me/theorems/2f928b39-68fb-58fc-a01c-b382661827a7
-- title:
--   Erdos919: T1 not inj
-- statement:
--   The Erdos919 construction uses the T1 not inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L556-L564
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L556-L564

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

theorem Erdos919.T1_not_inj (d : T1.{u} → ULift.{u} ℕ) : ∃ t₁ t₂, t₁ ≠ t₂ ∧ d t₁ = d t₂ := by sorry
