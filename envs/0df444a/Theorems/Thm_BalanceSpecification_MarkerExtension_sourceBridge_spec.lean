-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_sourceBridge_spec
-- name    : BalanceSpecification.MarkerExtension.sourceBridge_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:58.694971+00:00
-- url     : https://prove2.me/theorems/7904ea8b-5f6a-4e45-ab83-74f272bcf5fb
-- title:
--   Marker Extension: source Bridge spec
-- statement:
--   The Marker Extension construction uses the source Bridge spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L279-L287
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L279-L287

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
omit [DiscreteTopology A] [Fintype A] [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]

theorem BalanceSpecification.MarkerExtension.sourceBridge_spec {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) (u : PositiveLanguage Y) :
    sourceBridge M hM x s u ∈ language Y ∧
      (sourceBridge M hM x s u).length = M ∧
      u.val ++ sourceBridge M hM x s u ++ sourceTail x (suffixLength M s u.val.length) ∈ language Y := by sorry
