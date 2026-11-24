-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_exists_small_end
-- name    : BalanceSpecification.GapRead.exists_small_end
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:47:20.737826+00:00
-- url     : https://prove2.me/theorems/41f9de1f-dda4-44d7-8db1-71ff4b8e4a61
-- title:
--   Gap Read: exists small end
-- statement:
--   Uniform right completion permits a representation ending with a bounded
--   remaining gap, with the completely-zero word handled separately.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L213-L227
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L213-L227

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
open BalanceSpecification.GapRead
variable {S : Set ℕ} {N a b : ℕ} {w : Word Bool}

theorem BalanceSpecification.GapRead.exists_small_end
    (hN : ∀ t, GapState S t → ∃ s ∈ S, t ≤ s ∧ s ≤ t + N)
    (h : GapRead S a w b) (ha : GapState S a) :
    ∃ a' b', GapState S a' ∧ GapRead S a' w b' ∧ b' ≤ N := by sorry
