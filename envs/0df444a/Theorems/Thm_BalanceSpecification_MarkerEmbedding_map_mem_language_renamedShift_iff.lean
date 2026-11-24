-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerEmbedding_map_mem_language_renamedShift_iff
-- name    : BalanceSpecification.MarkerEmbedding.map_mem_language_renamedShift_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:20:12.983192+00:00
-- url     : https://prove2.me/theorems/e7617a5f-bd15-42ad-8ade-83cb573ce54d
-- title:
--   Marker Embedding: map mem language renamed Shift iff
-- statement:
--   The Marker Embedding construction uses the map mem language renamed Shift iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L67-L76
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerEmbedding.lean#L67-L76

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

theorem BalanceSpecification.MarkerEmbedding.map_mem_language_renamedShift_iff {f : A → B} (hf : Function.Injective f)
    {Y : ShiftSpace A} {v : Word A} :
    v.map f ∈ language (renamedShift f Y) ↔ v ∈ language Y := by sorry
