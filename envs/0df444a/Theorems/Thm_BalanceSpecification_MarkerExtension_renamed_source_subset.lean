-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_renamed_source_subset
-- name    : BalanceSpecification.MarkerExtension.renamed_source_subset
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:00:41.983802+00:00
-- url     : https://prove2.me/theorems/e0071a86-5ccf-48ab-a958-712aa28548db
-- title:
--   Marker Extension: renamed source subset
-- statement:
--   The renamed source is an actual subshift of the coded extension.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L403-L408
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L403-L408

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

theorem BalanceSpecification.MarkerExtension.renamed_source_subset :
    (MarkerEmbedding.renamedShift (some : A → Option A) Y).carrier ⊆ (shift M hM x s).carrier := by sorry
