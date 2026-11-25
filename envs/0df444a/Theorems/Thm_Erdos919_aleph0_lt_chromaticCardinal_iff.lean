-- Prove2me | Theorems.Thm_Erdos919_aleph0_lt_chromaticCardinal_iff
-- name    : Erdos919.aleph0_lt_chromaticCardinal_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:28:03.515073+00:00
-- url     : https://prove2.me/theorems/07006efb-14bd-4b6c-8406-e7c8c02084ba
-- title:
--   Erdos919: aleph0 lt chromatic Cardinal iff
-- statement:
--   The Erdos919 construction uses the aleph0 lt chromatic Cardinal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L676-L678
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L676-L678

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

theorem Erdos919.aleph0_lt_chromaticCardinal_iff {V : Type u} (G : SimpleGraph V) :
    ℵ₀ < G.chromaticCardinal ↔ IsEmpty (G.Coloring ℕ) := by sorry
