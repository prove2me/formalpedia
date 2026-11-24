-- Prove2me | Theorems.Thm_BalanceSpecification_getElem_block
-- name    : BalanceSpecification.getElem_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:18.284608+00:00
-- url     : https://prove2.me/theorems/a9e737b1-c0b8-4cdd-9459-372e47184d5d
-- title:
--   Balance Specification: get Elem block
-- statement:
--   The Balance Specification construction uses the get Elem block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean#L28-L30
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean#L28-L30

module
public import Mathlib.Dynamics.SymbolicDynamics.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Language
set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification

theorem BalanceSpecification.getElem_block {A : Type*} (x : Configuration A) (k : ℤ)
    (n i : ℕ) (hi : i < n) : (block x k n)[i]'(by simpa [block] using hi) = x (k + i) := by sorry
