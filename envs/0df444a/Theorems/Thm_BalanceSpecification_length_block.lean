-- Prove2me | Theorems.Thm_BalanceSpecification_length_block
-- name    : BalanceSpecification.length_block
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:30:19.307931+00:00
-- url     : https://prove2.me/theorems/12ea7dbe-8398-429c-a55a-3ddc09621ef1
-- title:
--   Balance Specification: length block
-- statement:
--   The Balance Specification construction uses the length block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean#L25-L26
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean#L25-L26

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

theorem BalanceSpecification.length_block {A : Type*} (x : Configuration A) (k : ℤ) (n : ℕ) :
    (block x k n).length = n := by sorry
