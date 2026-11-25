-- Prove2me | Theorems.Thm_Erdos919_Q_iff
-- name    : Erdos919.Q_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:28:13.921427+00:00
-- url     : https://prove2.me/theorems/e74caf3f-8e3d-51bd-8561-ebb0ec6ab3ae
-- title:
--   Erdos919: Q iff
-- statement:
--   The Erdos919 construction uses the Q iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L760-L769
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L760-L769

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

theorem Erdos919.Q_iff (κ : Cardinal.{u}) :
    Q κ ↔ ∃ G : SimpleGraph (W.{u} ×ₗ W.{u}), SmallTypeCC G ∧ G.chromaticCardinal = κ := by sorry
