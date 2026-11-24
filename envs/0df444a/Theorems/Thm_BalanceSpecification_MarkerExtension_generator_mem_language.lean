-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_generator_mem_language
-- name    : BalanceSpecification.MarkerExtension.generator_mem_language
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:01:58.531347+00:00
-- url     : https://prove2.me/theorems/68cefef6-ca1c-4034-94d7-c1994c739747
-- title:
--   Marker Extension: generator mem language
-- statement:
--   The Marker Extension construction uses the generator mem language property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L376-L379
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L376-L379

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
omit [DiscreteTopology A] [Fintype A] [DiscreteTopology (Option A)]

theorem BalanceSpecification.MarkerExtension.generator_mem_language (u : PositiveLanguage Y) :
    none :: (sourcePayload M hM x s u).map some ∈ language (shift M hM x s) := by sorry
