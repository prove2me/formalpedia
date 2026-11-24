-- Prove2me | Theorems.Thm_BalanceSpecification_exists_realization_generatedWords_at_cut
-- name    : BalanceSpecification.exists_realization_generatedWords_at_cut
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:23.759267+00:00
-- url     : https://prove2.me/theorems/ce359b22-29b2-4480-881a-ce28342e3741
-- title:
--   Balance Specification: exists realization generated Words at cut
-- statement:
--   Any finite concatenation occurs at a generator cut in an actual bi-infinite
--   concatenation, provided the code has a nonempty generator for the tails. Empty
--   generators in the finite concatenation are discarded without changing its word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L205-L243
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L205-L243

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

theorem BalanceSpecification.exists_realization_generatedWords_at_cut {C : Set (Word A)}
    (hC : ∃ q ∈ C, 0 < q.length) {v : Word A} (hv : v ∈ generatedWords C) :
    ∃ (x : Configuration A) (p : ℤ → ℤ), StrictMono p ∧ p 0 = 0 ∧
      (∀ i : ℤ, block x (p i) ((p (i + 1) - p i).toNat) ∈ C) ∧
      block x 0 v.length = v := by sorry
