-- Prove2me | Theorems.Thm_BalanceSpecification_block_subword
-- name    : BalanceSpecification.block_subword
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:13.888823+00:00
-- url     : https://prove2.me/theorems/908ea577-d38d-4dce-8085-2ed8b5590d86
-- title:
--   Balance Specification: block subword
-- statement:
--   Taking a subword commutes with extracting a larger block.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean#L81-L97
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Language.lean#L81-L97

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

theorem BalanceSpecification.block_subword {A : Type*} (x : Configuration A) (k : ℤ)
    (p u q : Word A) (h : block x k (p ++ u ++ q).length = p ++ u ++ q) :
    block x (k + p.length) u.length = u := by sorry
