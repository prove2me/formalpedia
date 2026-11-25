-- Prove2me | Theorems.Thm_Erdos919_smallCard_iff
-- name    : Erdos919.smallCard_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:33:21.200863+00:00
-- url     : https://prove2.me/theorems/ef8f2630-7e32-5adf-88f5-a12f3d2e39f5
-- title:
--   Erdos919: small Card iff
-- statement:
--   The Erdos919 construction uses the small Card iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L799-L806
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L799-L806

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

theorem Erdos919.smallCard_iff {V : Type u} (hV : #V = ℵ_ 2) (G : SimpleGraph V) :
    SmallCardCC G ↔ ∀ (X : Set V) (_ : #X = ℵ₁), (G.induce X).chromaticCardinal ≤ ℵ₀ := by sorry
