-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_map_word_mem_language_iff
-- name    : BalanceSpecification.MarkerExtension.map_word_mem_language_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:45.373953+00:00
-- url     : https://prove2.me/theorems/39c6eead-d5cd-4b23-97ad-a747acf49504
-- title:
--   Marker Extension: map word mem language iff
-- statement:
--   A marker-free word in the construction is exactly a renamed word of Y.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L425-L437
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L425-L437

module
public import Definitions.Def_BalanceSpecificaton_MarkerEmbedding
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Synchronization
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A] [Fintype A]

theorem BalanceSpecification.MarkerExtension.map_word_mem_language_iff {v : Word A} :
    v.map some ∈ language (shift M hM x s) ↔ v ∈ language Y := by sorry
