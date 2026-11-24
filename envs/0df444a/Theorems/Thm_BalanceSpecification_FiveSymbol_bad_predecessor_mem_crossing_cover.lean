-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_bad_predecessor_mem_crossing_cover
-- name    : BalanceSpecification.FiveSymbol.bad_predecessor_mem_crossing_cover
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:37.162187+00:00
-- url     : https://prove2.me/theorems/49dd1d18-6b3a-46a4-a97b-ec576e3ccca6
-- title:
--   Five Symbol: bad predecessor mem crossing cover
-- statement:
--   The Five Symbol construction uses the bad predecessor mem crossing cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L163-L191
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L163-L191

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

theorem BalanceSpecification.FiveSymbol.bad_predecessor_mem_crossing_cover {u v : Word Alphabet}
    (hu : u ∈ language shift) (hv : v ∈ language shift)
    (hbad : v ++ u ∉ language shift) :
    ∃ l : ℕ, 1 ≤ l ∧ l ≤ v.length ∧ v ∈ leftCrossingCover v.length l := by sorry
