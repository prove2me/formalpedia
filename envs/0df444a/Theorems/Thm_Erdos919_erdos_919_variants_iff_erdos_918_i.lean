-- Prove2me | Theorems.Thm_Erdos919_erdos_919_variants_iff_erdos_918_i
-- name    : Erdos919.erdos_919.variants.iff_erdos_918_i
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:36:57.459282+00:00
-- url     : https://prove2.me/theorems/0e9b428a-cbbd-4d88-9afe-6df1ee91d0a9
-- title:
--   variants: iff erdos 918 i
-- statement:
--   `erdos_919.variants.iff_erdos_918_i`: the `ℵ₂` version of Problem 919 is equivalent to
--   Problem 918(i).
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L860-L866
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L860-L866

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919

theorem Erdos919.erdos_919.variants.iff_erdos_918_i :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) ↔
    ∃ (V : Type u) (G : SimpleGraph V), #V = ℵ_ 2 ∧ G.chromaticCardinal = ℵ_ 2 ∧
      ∀ (W : Set V) (_ : #W = ℵ₁), (G.induce W).chromaticCardinal ≤ ℵ₀ := by sorry
