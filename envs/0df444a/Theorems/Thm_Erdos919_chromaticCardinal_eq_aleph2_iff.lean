-- Prove2me | Theorems.Thm_Erdos919_chromaticCardinal_eq_aleph2_iff
-- name    : Erdos919.chromaticCardinal_eq_aleph2_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:28:10.566281+00:00
-- url     : https://prove2.me/theorems/58053d53-fe82-4c1f-8120-a4952d64c6f1
-- title:
--   Erdos919: chromatic Cardinal eq aleph2 iff
-- statement:
--   The Erdos919 construction uses the chromatic Cardinal eq aleph2 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L680-L696
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L680-L696

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

theorem Erdos919.chromaticCardinal_eq_aleph2_iff {V : Type u} (G : SimpleGraph V) (hV : #V = ℵ_ 2) :
    G.chromaticCardinal = ℵ_ 2 ↔ ChiAleph2 G := by sorry
