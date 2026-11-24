-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_length
-- name    : BalanceSpecification.MarkerExtension.sourcePayload_length
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:55.965138+00:00
-- url     : https://prove2.me/theorems/48adbdd1-11e7-4e6a-8e87-5b540959ef54
-- title:
--   Marker Extension: source Payload length
-- statement:
--   The Marker Extension construction uses the source Payload length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L353-L356
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L353-L356

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
omit [DiscreteTopology A] [Fintype A] [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]

theorem BalanceSpecification.MarkerExtension.sourcePayload_length (u : PositiveLanguage Y) :
    (sourcePayload M hM x s u).length = u.val.length + M + suffixLength M s u.val.length := by sorry
