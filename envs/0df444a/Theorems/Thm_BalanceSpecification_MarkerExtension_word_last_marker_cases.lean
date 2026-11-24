-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_word_last_marker_cases
-- name    : BalanceSpecification.MarkerExtension.word_last_marker_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:16.496581+00:00
-- url     : https://prove2.me/theorems/2a4705c3-c419-476c-ba22-92d88d502915
-- title:
--   Marker Extension: word last marker cases
-- statement:
--   The last-marker partition is an exact statement about actual admissible
--   words, with its remaining marker-free suffix a source word.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L470-L484
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerExtension.lean#L470-L484

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

theorem BalanceSpecification.MarkerExtension.word_last_marker_cases {w : Word (Option A)}
    (hw : w ∈ language (shift M hM x s)) :
    (∃ v ∈ language Y, w = v.map some) ∨
      ∃ u : Word (Option A), ∃ v ∈ language Y,
        u ++ [none] ∈ language (shift M hM x s) ∧ w = (u ++ [none]) ++ v.map some := by sorry
