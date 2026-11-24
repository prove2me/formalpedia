-- Prove2me | Theorems.Thm_BalanceSpecification_IsConcatenation_block_infix_generatedWords
-- name    : BalanceSpecification.IsConcatenation.block_infix_generatedWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:21.7378+00:00
-- url     : https://prove2.me/theorems/5ca3ed4e-927d-499f-b004-118addc380f9
-- title:
--   Is Concatenation: block infix generated Words
-- statement:
--   Every finite block of a literal bi-infinite concatenation is a contiguous
--   subword of a finite concatenation of generators.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L79-L100
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L79-L100

module
public import Definitions.Def_BalanceSpecificaton_Coded
public import Definitions.Def_BalanceSpecificaton_Forbidden
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
variable {A : Type*}

theorem BalanceSpecification.IsConcatenation.block_infix_generatedWords {C : Set (Word A)}
    {x : Configuration A} (hx : IsConcatenation C x) (k : ℤ) (n : ℕ) :
    ∃ v ∈ generatedWords C, block x k n <:+: v := by sorry
