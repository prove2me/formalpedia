-- Prove2me | Theorems.Thm_Erdos919_Q_aleph1_iff
-- name    : Erdos919.Q_aleph1_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:18:31.154785+00:00
-- url     : https://prove2.me/theorems/f7e2bb9b-a60b-5773-b972-1fe6d25e3db7
-- title:
--   Erdos919: Q aleph1 iff
-- statement:
--   The Erdos919 construction uses the Q aleph1 iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L777-L781
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L777-L781

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

theorem Erdos919.Q_aleph1_iff :
    Q.{u} ℵ₁ ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ ChiAleph1 G := by sorry
