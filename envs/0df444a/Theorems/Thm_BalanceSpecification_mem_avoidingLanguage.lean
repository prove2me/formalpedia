-- Prove2me | Theorems.Thm_BalanceSpecification_mem_avoidingLanguage
-- name    : BalanceSpecification.mem_avoidingLanguage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:32:01.245805+00:00
-- url     : https://prove2.me/theorems/64e6916d-8972-40c5-84a1-4b689258301f
-- title:
--   Balance Specification: mem avoiding Language
-- statement:
--   The Balance Specification construction uses the mem avoiding Language property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L33-L34
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/Occurrence.lean#L33-L34

module
public import Definitions.Def_BalanceSpecificaton_Counting
public import Definitions.Def_BalanceSpecificaton_Growth
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Occurrence
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
open Filter
open scoped Topology
variable {A : Type*} [Fintype A] {L : Set (Word A)}
omit [Fintype A]

theorem BalanceSpecification.mem_avoidingLanguage {v w : Word A} :
    w ∈ avoidingLanguage L v ↔ w ∈ L ∧ ¬v <:+: w := by sorry
