-- Prove2me | Theorems.Thm_Erdos919_inc_iff
-- name    : Erdos919.inc_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:33:38.628553+00:00
-- url     : https://prove2.me/theorems/ae4f231b-25f9-4cbf-9ac8-d588c44fd22d
-- title:
--   Erdos919: inc iff
-- statement:
--   The Erdos919 construction uses the inc iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L831-L838
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L831-L838

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

theorem Erdos919.inc_iff :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ IsEmpty (H.Coloring ℕ) := by sorry
