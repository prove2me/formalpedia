-- Prove2me | Theorems.Thm_Erdos919_induce_le_aleph0_iff
-- name    : Erdos919.induce_le_aleph0_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:25:57.739846+00:00
-- url     : https://prove2.me/theorems/5f94831c-799e-405f-90d8-0bbe86d62f36
-- title:
--   Erdos919: induce le aleph0 iff
-- statement:
--   The Erdos919 construction uses the induce le aleph0 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L672-L674
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L672-L674

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

theorem Erdos919.induce_le_aleph0_iff {V : Type u} (G : SimpleGraph V) (X : Set V) :
    (G.induce X).chromaticCardinal ≤ ℵ₀ ↔ ColorableOn G X ℕ := by sorry
