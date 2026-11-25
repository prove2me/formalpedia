-- Prove2me | Theorems.Thm_Erdos919_erdos_919_variants_aleph_1_iff
-- name    : Erdos919.erdos_919.variants.aleph_1_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:36:59.999286+00:00
-- url     : https://prove2.me/theorems/76ff95bb-affd-549d-a486-aa60d0d217bf
-- title:
--   variants: aleph 1 iff
-- statement:
--   `erdos_919.variants.aleph_1_iff`: the `ℵ₁` version of Problem 919 is equivalent to the
--   existence of a graph on `ℵ₂` vertices that is not countably chromatic although every subgraph
--   on `ℵ₁` vertices is.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L871-L877
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L871-L877

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919

theorem Erdos919.erdos_919.variants.aleph_1_iff :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ ℵ₀ < G.chromaticCardinal ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by sorry
