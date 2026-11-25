-- Prove2me | Theorems.Thm_Erdos919_size_iff
-- name    : Erdos919.size_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:29:09.772431+00:00
-- url     : https://prove2.me/theorems/5a47f803-f7d4-5aa0-9063-aa86d0cf10e8
-- title:
--   Erdos919: size iff
-- statement:
--   Graphs of size `ℵ₂` can be moved to `W`.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L809-L820
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L809-L820

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

theorem Erdos919.size_iff (P : ∀ {V : Type u}, SimpleGraph V → Prop)
    (hP : ∀ {A B : Type u} (e : A ≃ B) (G : SimpleGraph B), P (G.comap e) ↔ P G) :
    (∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ P G ∧
      ∀ (X : Set V) (_ : #X = ℵ₁), (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ P H := by sorry
