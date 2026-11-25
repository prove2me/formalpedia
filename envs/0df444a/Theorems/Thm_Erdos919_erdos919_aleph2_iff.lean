-- Prove2me | Theorems.Thm_Erdos919_erdos919_aleph2_iff
-- name    : Erdos919.erdos919_aleph2_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:24:41.387022+00:00
-- url     : https://prove2.me/theorems/749baa0b-7b17-4cbc-a59a-c7238aef5bbf
-- title:
--   Erdos919: erdos919 aleph2 iff
-- statement:
--   The `ℵ₂` version is equivalent to the existence of an `(ℵ₀, ℵ₂)`-chromatic graph of size
--   `ℵ₂`.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L538-L549
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L538-L549

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

theorem Erdos919.erdos919_aleph2_iff :
    (∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph2 G) ↔
      ∃ H : SimpleGraph W.{u}, SmallCardCC H ∧ ChiAleph2 H := by sorry
