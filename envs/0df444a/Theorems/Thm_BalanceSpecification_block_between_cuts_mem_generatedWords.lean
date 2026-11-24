-- Prove2me | Theorems.Thm_BalanceSpecification_block_between_cuts_mem_generatedWords
-- name    : BalanceSpecification.block_between_cuts_mem_generatedWords
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:22.254631+00:00
-- url     : https://prove2.me/theorems/9d0c8ae8-3af9-43b9-bf29-21592d845d62
-- title:
--   Balance Specification: block between cuts mem generated Words
-- statement:
--   Reading between finitely many consecutive generator cuts gives an actual
--   finite concatenation of generators.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L51-L75
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L51-L75

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

theorem BalanceSpecification.block_between_cuts_mem_generatedWords {C : Set (Word A)}
    {x : Configuration A} {p : ℤ → ℤ} (hp : StrictMono p)
    (hwords : ∀ i : ℤ, block x (p i) ((p (i + 1) - p i).toNat) ∈ C)
    (i : ℤ) (n : ℕ) :
    block x (p i) ((p (i + n) - p i).toNat) ∈ generatedWords C := by sorry
