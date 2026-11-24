-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_hasSpecification_renamedShift
-- name    : BalanceSpecification.MarkerEmbedding.hasSpecification_renamedShift
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:56:06.250934+00:00
-- url     : https://prove2.me/theorems/cf97eab8-db71-4d54-8921-830e492bb559
-- title:
--   Marker Embedding: has Specification renamed Shift
-- statement:
--   Specification gaps are preserved by coordinatewise alphabet renaming.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L112-L123
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L112-L123

module
public import Definitions.Def_BalanceSpecificaton_Entropy
public import Definitions.Def_BalanceSpecificaton_Specification
public import Definitions.Def_BalanceSpecificaton_LanguageProperties
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerEmbedding
variable {A B : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace B] [T2Space B]

theorem BalanceSpecification.MarkerEmbedding.hasSpecification_renamedShift (f : A → B) {Y : ShiftSpace A}
    (hY : HasSpecification Y) : HasSpecification (renamedShift f Y) := by sorry
