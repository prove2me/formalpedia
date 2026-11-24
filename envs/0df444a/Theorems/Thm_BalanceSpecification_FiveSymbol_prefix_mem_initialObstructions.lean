-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_prefix_mem_initialObstructions
-- name    : BalanceSpecification.FiveSymbol.prefix_mem_initialObstructions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:32.117131+00:00
-- url     : https://prove2.me/theorems/52f823af-4ea6-40af-a6ba-e8ea66ffda54
-- title:
--   Five Symbol: prefix mem initial Obstructions
-- statement:
--   The Five Symbol construction uses the prefix mem initial Obstructions property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L109-L121
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbolBalance.lean#L109-L121

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

theorem BalanceSpecification.FiveSymbol.prefix_mem_initialObstructions {s : Word Alphabet} {j l : ℕ}
    (hs : s <+: forbiddenWord j) (hlen : s.length = l) (hl : 0 < l) :
    s ∈ initialObstructions l := by sorry
