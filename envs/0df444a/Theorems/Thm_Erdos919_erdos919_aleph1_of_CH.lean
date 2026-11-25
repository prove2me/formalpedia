-- Prove2me | Theorems.Thm_Erdos919_erdos919_aleph1_of_CH
-- name    : Erdos919.erdos919_aleph1_of_CH
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:55.95552+00:00
-- url     : https://prove2.me/theorems/da16946a-7cd6-4559-8472-67338b248476
-- title:
--   Erdos919: erdos919 aleph1 of CH
-- statement:
--   Under CH the `ℵ₁` version has a positive answer, via the Erdős-Hajnal shift graph.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L594-L637
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L594-L637

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

theorem Erdos919.erdos919_aleph1_of_CH (hCH : (𝔠 : Cardinal.{0}) = ℵ₁) :
    ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G := by sorry
