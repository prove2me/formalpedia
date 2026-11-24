-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_mem_language_renamedShift_iff
-- name    : BalanceSpecification.MarkerEmbedding.mem_language_renamedShift_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:33:39.200584+00:00
-- url     : https://prove2.me/theorems/97d3f8f8-b6cf-4937-9c91-4f4f383e8536
-- title:
--   Marker Embedding: mem language renamed Shift iff
-- statement:
--   Alphabet renaming acts on the complete finite language by list map.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L57-L65
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L57-L65

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

theorem BalanceSpecification.MarkerEmbedding.mem_language_renamedShift_iff (f : A → B) {Y : ShiftSpace A} {w : Word B} :
    w ∈ language (renamedShift f Y) ↔ ∃ v ∈ language Y, v.map f = w := by sorry
