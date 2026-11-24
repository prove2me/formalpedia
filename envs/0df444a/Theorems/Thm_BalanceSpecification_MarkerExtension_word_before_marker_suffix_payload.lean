-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_word_before_marker_suffix_payload
-- name    : BalanceSpecification.MarkerExtension.word_before_marker_suffix_payload
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:07.28526+00:00
-- url     : https://prove2.me/theorems/abf9871a-257a-4dc2-a536-758f303f467a
-- title:
--   Marker Extension: word before marker suffix payload
-- statement:
--   A marker-free word immediately before a marker is a suffix of a genuine
--   source payload. This supplies the common-tail counting packet.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L450-L465
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L450-L465

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

theorem BalanceSpecification.MarkerExtension.word_before_marker_suffix_payload {v : Word A}
    (hv : v.map some ++ [none] ∈ language (shift M hM x s)) :
    ∃ u : PositiveLanguage Y, v <:+ sourcePayload M hM x s u := by sorry
