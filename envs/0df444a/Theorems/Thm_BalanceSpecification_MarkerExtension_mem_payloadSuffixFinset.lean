-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_mem_payloadSuffixFinset
-- name    : BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:59:57.006799+00:00
-- url     : https://prove2.me/theorems/13ab3eef-7fcd-48b3-94d3-8bfe4eb7e8cd
-- title:
--   Marker Extension: mem payload Suffix Finset
-- statement:
--   The Marker Extension construction uses the mem payload Suffix Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L84-L89
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L84-L89

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
variable [Fintype A]

theorem BalanceSpecification.MarkerExtension.mem_payloadSuffixFinset {l : ℕ} {z : Word A} :
    z ∈ payloadSuffixFinset M hM x s l ↔
      z ∈ language Y ∧ z.length = l ∧
        ∃ u : PositiveLanguage Y, z <:+ sourcePayload M hM x s u := by sorry
