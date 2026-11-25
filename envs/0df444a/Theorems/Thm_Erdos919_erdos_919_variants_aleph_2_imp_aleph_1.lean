-- Prove2me | Theorems.Thm_Erdos919_erdos_919_variants_aleph_2_imp_aleph_1
-- name    : Erdos919.erdos_919.variants.aleph_2_imp_aleph_1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:37:15.828491+00:00
-- url     : https://prove2.me/theorems/4a2bdc12-b5c7-5a02-8ba5-b69538179fb3
-- title:
--   variants: aleph 2 imp aleph 1
-- statement:
--   `erdos_919.variants.aleph_2_imp_aleph_1`: a positive answer to the `ℵ₂` version gives a
--   positive answer to the `ℵ₁` version.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L881-L891
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L881-L891

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919

theorem Erdos919.erdos_919.variants.aleph_2_imp_aleph_1 :
    (∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ_ 2 ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀) →
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by sorry
