-- Prove2me | Theorems.Thm_BalanceSpecification_exists_prepend_generator_concatenation
-- name    : BalanceSpecification.exists_prepend_generator_concatenation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:56:22.797632+00:00
-- url     : https://prove2.me/theorems/f6a7e378-3c3b-4fb9-a801-d46b2b08c839
-- title:
--   Balance Specification: exists prepend generator concatenation
-- statement:
--   A generator can be prepended at a generator cut, keeping an actual
--   bi-infinite generator decomposition rather than a substitute language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L116-L200
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/CodedLanguage.lean#L116-L200

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

theorem BalanceSpecification.exists_prepend_generator_concatenation {C : Set (Word A)} {v : Word A}
    (hvC : v ∈ C) (hv : 0 < v.length) {y : Configuration A} {p : ℤ → ℤ}
    (hp : StrictMono p) (hp0 : p 0 = 0)
    (hwords : ∀ i : ℤ, block y (p i) ((p (i + 1) - p i).toNat) ∈ C) :
    ∃ (z : Configuration A) (q : ℤ → ℤ), StrictMono q ∧ q 0 = 0 ∧
      (∀ i : ℤ, block z (q i) ((q (i + 1) - q i).toNat) ∈ C) ∧
      ∀ n : ℕ, block z 0 (v.length + n) = v ++ block y 0 n := by sorry
