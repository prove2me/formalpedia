-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_sourcePayload_length_of_large
-- name    : BalanceSpecification.MarkerExtension.sourcePayload_length_of_large
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:36.569188+00:00
-- url     : https://prove2.me/theorems/bec30215-79a4-468d-af10-7c8ecc6f0db3
-- title:
--   Marker Extension: source Payload length of large
-- statement:
--   The Marker Extension construction uses the source Payload length of large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L359-L365
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L359-L365

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

theorem BalanceSpecification.MarkerExtension.sourcePayload_length_of_large
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) (u : PositiveLanguage Y) :
    (sourcePayload M hM x s u).length = s u.val.length := by sorry
