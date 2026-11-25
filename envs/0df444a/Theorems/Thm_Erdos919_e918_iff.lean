-- Prove2me | Theorems.Thm_Erdos919_e918_iff
-- name    : Erdos919.e918_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:33:33.305874+00:00
-- url     : https://prove2.me/theorems/e1534006-e541-442e-ac70-08ac121bdb33
-- title:
--   Erdos919: e918 iff
-- statement:
--   The Erdos919 construction uses the e918 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L822-L829
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L822-L829

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

theorem Erdos919.e918_iff :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ ChiAleph2 H := by sorry
