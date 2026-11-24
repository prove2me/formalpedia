-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_map_word_mem_language
-- name    : BalanceSpecification.MarkerExtension.map_word_mem_language
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:29.87988+00:00
-- url     : https://prove2.me/theorems/7d07abf6-00d5-4af4-9ebb-588a05d7496f
-- title:
--   Marker Extension: map word mem language
-- statement:
--   The entire renamed source language is contained in the extension language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L397-L400
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L397-L400

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

theorem BalanceSpecification.MarkerExtension.map_word_mem_language {v : Word A} (hv : v ∈ language Y) :
    v.map some ∈ language (shift M hM x s) := by sorry
