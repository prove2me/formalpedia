-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_bad_follower_mem_crossing_cover
-- name    : BalanceSpecification.FiveSymbol.bad_follower_mem_crossing_cover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:34.156088+00:00
-- url     : https://prove2.me/theorems/a1ccaa52-182f-45e3-8ab4-7120e5451acf
-- title:
--   Five Symbol: bad follower mem crossing cover
-- statement:
--   The Five Symbol construction uses the bad follower mem crossing cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L133-L161
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L133-L161

module
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
public import Definitions.Def_BalanceSpecificaton_CountBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbolBalance
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.bad_follower_mem_crossing_cover {u v : Word Alphabet}
    (hu : u ∈ language shift) (hv : v ∈ language shift)
    (hbad : u ++ v ∉ language shift) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ v.length ∧ v ∈ rightCrossingCover v.length l := by sorry
