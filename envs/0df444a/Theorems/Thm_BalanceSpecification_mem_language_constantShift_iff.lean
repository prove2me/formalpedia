-- Prove2me | Theorems.Thm_BalanceSpecification_mem_language_constantShift_iff
-- name    : BalanceSpecification.mem_language_constantShift_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:54.288623+00:00
-- url     : https://prove2.me/theorems/9efbe556-4b61-43fb-a13c-a90daaaefca3
-- title:
--   Balance Specification: mem language constant Shift iff
-- statement:
--   The Balance Specification construction uses the mem language constant Shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L229-L238
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/ProductShift.lean#L229-L238

module
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_TilingBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_ProductShift
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A B : Type*}

theorem BalanceSpecification.mem_language_constantShift_iff [TopologicalSpace A] [T1Space A]
    (a : A) {w : Word A} :
    w ∈ language (constantShift a) ↔ w = List.replicate w.length a := by sorry
