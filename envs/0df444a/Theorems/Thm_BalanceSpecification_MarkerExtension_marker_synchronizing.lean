-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marker_synchronizing
-- name    : BalanceSpecification.MarkerExtension.marker_synchronizing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:59:51.471978+00:00
-- url     : https://prove2.me/theorems/391cff07-3abc-412d-89c8-3cdfecbd8e3c
-- title:
--   Marker Extension: marker synchronizing
-- statement:
--   The Marker Extension construction uses the marker synchronizing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L333-L339
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L333-L339

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
omit [DiscreteTopology A] [Fintype A]

theorem BalanceSpecification.MarkerExtension.marker_synchronizing {Y : ShiftSpace A} (M : ℕ)
    (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
      ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
    (x : Y.carrier) (s : ℕ → ℕ) : IsSynchronizing (language (shift M hM x s)) [none] := by sorry
