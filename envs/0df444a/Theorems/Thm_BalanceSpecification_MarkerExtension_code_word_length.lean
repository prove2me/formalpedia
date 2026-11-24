-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_code_word_length
-- name    : BalanceSpecification.MarkerExtension.code_word_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:23:45.371244+00:00
-- url     : https://prove2.me/theorems/d662ea33-632d-4aa9-b885-62c4ac955e76
-- title:
--   Marker Extension: code word length
-- statement:
--   The Marker Extension construction uses the code word length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L368-L373
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L368-L373

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

theorem BalanceSpecification.MarkerExtension.code_word_length (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n)
    {z : Word (Option A)} (hz : z ∈ code M hM x s) :
    ∃ n : ℕ, 1 ≤ n ∧ z.length = s n + 1 := by sorry
