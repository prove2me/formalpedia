-- Prove2me | Theorems.Thm_Erdos919_chromaticCardinal_le_aleph0_iff
-- name    : Erdos919.chromaticCardinal_le_aleph0_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:24:50.27606+00:00
-- url     : https://prove2.me/theorems/08a198d9-375d-41a7-a7a3-873279f34e28
-- title:
--   Erdos919: chromatic Cardinal le aleph0 iff
-- statement:
--   The Erdos919 construction uses the chromatic Cardinal le aleph0 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L661-L670
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L661-L670

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

theorem Erdos919.chromaticCardinal_le_aleph0_iff {V : Type u} (G : SimpleGraph V) :
    G.chromaticCardinal ≤ ℵ₀ ↔ Nonempty (G.Coloring ℕ) := by sorry
