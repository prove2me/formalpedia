-- Prove2me | Theorems.Thm_BalanceSpecification_shortlexWord_strictMono
-- name    : BalanceSpecification.shortlexWord_strictMono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:09:30.829798+00:00
-- url     : https://prove2.me/theorems/d92eeb9b-9dd7-46f0-9ecb-a7956328ea59
-- title:
--   Balance Specification: shortlex Word strict Mono
-- statement:
--   The Balance Specification construction uses the shortlex Word strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L113-L119
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Shortlex.lean#L113-L119

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Mathlib.Data.List.Shortlex
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Shortlex
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [LinearOrder A]
variable [Nonempty A]

theorem BalanceSpecification.shortlexWord_strictMono {i j : ℕ} (hij : i < j) :
    List.Shortlex (· < ·) (shortlexWord (A := A) i) (shortlexWord j) := by sorry
