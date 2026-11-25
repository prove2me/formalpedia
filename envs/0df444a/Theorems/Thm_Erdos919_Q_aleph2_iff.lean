-- Prove2me | Theorems.Thm_Erdos919_Q_aleph2_iff
-- name    : Erdos919.Q_aleph2_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:29:27.225487+00:00
-- url     : https://prove2.me/theorems/d1f41757-6437-406b-ac8d-cd5889b19122
-- title:
--   Erdos919: Q aleph2 iff
-- statement:
--   The Erdos919 construction uses the Q aleph2 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L771-L775
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L771-L775

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

theorem Erdos919.Q_aleph2_iff :
    Q.{u} (ℵ_ 2) ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph2 G := by sorry
