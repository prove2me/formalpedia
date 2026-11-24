-- Prove2me | Theorems.Thm_BalanceSpecification_GapRead_small_end_of_true_mem
-- name    : BalanceSpecification.GapRead.small_end_of_true_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:03.180808+00:00
-- url     : https://prove2.me/theorems/23792247-e2ce-4dc5-9826-67a059a38eea
-- title:
--   Gap Read: small end of true mem
-- statement:
--   The Gap Read construction uses the small end of true mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L187-L209
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/SGap.lean#L187-L209

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

theorem BalanceSpecification.GapRead.small_end_of_true_mem
    (hN : ∀ t, GapState S t → ∃ s ∈ S, t ≤ s ∧ s ≤ t + N)
    (h : GapRead S a w b) (ht : true ∈ w) :
    ∃ b', b' ≤ N ∧ GapRead S a w b' := by sorry
