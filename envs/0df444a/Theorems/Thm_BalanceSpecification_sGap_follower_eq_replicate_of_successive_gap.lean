-- Prove2me | Theorems.Thm_BalanceSpecification_sGap_follower_eq_replicate_of_successive_gap
-- name    : BalanceSpecification.sGap_follower_eq_replicate_of_successive_gap
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:20.911374+00:00
-- url     : https://prove2.me/theorems/57c9218c-45a5-4be0-871b-b368e41c71fc
-- title:
--   Balance Specification: s Gap follower eq replicate of successive gap
-- statement:
--   Crossing a long consecutive gap forces every short follower of
--   `1 0^(a+1)` to consist of zeros.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L310-L323
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L310-L323

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification

theorem BalanceSpecification.sGap_follower_eq_replicate_of_successive_gap
    [TopologicalSpace Bool] [DiscreteTopology Bool] {S : Set ℕ} (hS : S.Nonempty)
    {a b k : ℕ} (hnext : ∀ s ∈ S, a < s → b ≤ s) (hgap : a + k < b)
    {w : Word Bool}
    (hw : (true :: List.replicate (a + 1) false) ++ w ∈ language (sGapShift S))
    (hlen : w.length = k) : w = List.replicate k false := by sorry
