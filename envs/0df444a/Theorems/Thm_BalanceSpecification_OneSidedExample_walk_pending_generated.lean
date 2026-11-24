-- Prove2me | Theorems.Thm_BalanceSpecification_OneSidedExample_walk_pending_generated
-- name    : BalanceSpecification.OneSidedExample.walk_pending_generated
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:53.885928+00:00
-- url     : https://prove2.me/theorems/24e4d690-a942-4cb7-b64d-c3dad2630547
-- title:
--   One Sided Example: walk pending generated
-- statement:
--   Reading a closed path, including partially read ascending or descending
--   excursions, yields finite concatenations of exactly the source generators.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L16-L85
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/OneSidedGraphLanguage.lean#L16-L85

module
public import Definitions.Def_BalanceSpecificaton_OneSidedGraph
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_OneSidedGraphLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification BalanceSpecification.OneSidedExample

theorem BalanceSpecification.OneSidedExample.walk_pending_generated (w : Word Alphabet) :
    (Walk (.p 0) w (.p 0) → w ∈ generatedWords code) ∧
    (∀ n : ℕ, Walk (.q n) w (.p 0) →
      List.replicate (n + 1) a ++ w ∈ generatedWords code) ∧
    (∀ d m : ℕ, 0 < d → 1 ≤ m → Walk (.p d) w (.p 0) →
      List.replicate (d + m) a ++ List.replicate m b ++ w ∈ generatedWords code) := by sorry
