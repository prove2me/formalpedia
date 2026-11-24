-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_marker_followed_by_word
-- name    : BalanceSpecification.MarkerExtension.marker_followed_by_word
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:00:41.544693+00:00
-- url     : https://prove2.me/theorems/84793a9a-57c8-460a-9c7a-d3606b25ff41
-- title:
--   Marker Extension: marker followed by word
-- statement:
--   Every source word can immediately follow the marker in the coded extension.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L383-L393
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L383-L393

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

theorem BalanceSpecification.MarkerExtension.marker_followed_by_word {v : Word A} (hv : v ∈ language Y) :
    [none] ++ v.map some ∈ language (shift M hM x s) := by sorry
