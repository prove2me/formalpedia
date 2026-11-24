-- Prove2me | Theorems.Thm_BalanceSpecification_FiveSymbol_block_padded_infix
-- name    : BalanceSpecification.FiveSymbol.block_padded_infix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:49.973805+00:00
-- url     : https://prove2.me/theorems/e0135490-4afc-4235-be3d-38af32ced3ac
-- title:
--   Five Symbol: block padded infix
-- statement:
--   A block entirely within the unpadded interval is a subword of `w`.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L98-L116
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/FiveSymbol.lean#L98-L116

module
public import Definitions.Def_BalanceSpecificaton_Shortlex
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_FiveSymbol
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.FiveSymbol

theorem BalanceSpecification.FiveSymbol.block_padded_infix (w : Word Alphabet) {k : ℤ} {n : ℕ}
    (hk : 0 ≤ k) (hend : k + (n : ℤ) ≤ w.length) :
    block (padded w) k n <:+: w := by sorry
