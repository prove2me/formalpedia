-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_synchronized
-- name    : BalanceSpecification.MarkerExtension.synchronized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:58.029407+00:00
-- url     : https://prove2.me/theorems/72855fdf-0eaa-430d-b63d-9b485818acf8
-- title:
--   Marker Extension: synchronized
-- statement:
--   The construction is synchronized before any counting estimates are invoked.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L420-L421
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L420-L421

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

theorem BalanceSpecification.MarkerExtension.synchronized : Synchronized (shift M hM x s) := by sorry
