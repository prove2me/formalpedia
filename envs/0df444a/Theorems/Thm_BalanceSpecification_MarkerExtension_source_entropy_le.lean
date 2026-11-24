-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_source_entropy_le
-- name    : BalanceSpecification.MarkerExtension.source_entropy_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:11.063709+00:00
-- url     : https://prove2.me/theorems/af2f6715-cb9c-45ab-a45b-32713a934187
-- title:
--   Marker Extension: source entropy le
-- statement:
--   Inclusion of the renamed source gives the lower entropy bound.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L411-L416
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L411-L416

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

theorem BalanceSpecification.MarkerExtension.source_entropy_le (hY : Y.carrier.Nonempty) :
    entropy Y hY ≤ entropy (shift M hM x s) (shift_nonempty M hM x s) := by sorry
