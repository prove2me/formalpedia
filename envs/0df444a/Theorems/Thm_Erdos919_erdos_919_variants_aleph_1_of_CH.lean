-- Prove2me | Theorems.Thm_Erdos919_erdos_919_variants_aleph_1_of_CH
-- name    : Erdos919.erdos_919.variants.aleph_1_of_CH
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:37:45.049922+00:00
-- url     : https://prove2.me/theorems/665ad64f-ba62-43eb-926c-0032806857de
-- title:
--   variants: aleph 1 of CH
-- statement:
--   `erdos_919.variants.aleph_1_of_CH`: under the continuum hypothesis the `ℵ₁` version has a
--   positive answer.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L895-L899
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L895-L899

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919

theorem Erdos919.erdos_919.variants.aleph_1_of_CH (hCH : 𝔠 = ℵ₁) :
    ∃ G : SimpleGraph (ω_ 2 ^ 2 : Ordinal.{u}).ToType, G.chromaticCardinal = ℵ₁ ∧
      ∀ X : Set (ω_ 2 ^ 2 : Ordinal.{u}).ToType, typeLT X < ω_ 2 ^ 2 →
        (G.induce X).chromaticCardinal ≤ ℵ₀ := by sorry
