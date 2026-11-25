-- Prove2me | Theorems.Thm_Erdos919_chromaticCardinal_eq_aleph1_iff
-- name    : Erdos919.chromaticCardinal_eq_aleph1_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:54.479806+00:00
-- url     : https://prove2.me/theorems/ee57b8dc-223a-5478-ae87-29c119e422ba
-- title:
--   Erdos919: chromatic Cardinal eq aleph1 iff
-- statement:
--   The Erdos919 construction uses the chromatic Cardinal eq aleph1 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L698-L709
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L698-L709

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

theorem Erdos919.chromaticCardinal_eq_aleph1_iff {V : Type u} (G : SimpleGraph V) :
    G.chromaticCardinal = ℵ₁ ↔ ChiAleph1 G := by sorry
