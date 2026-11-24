-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_wordCount_le_lastMarker_sum
-- name    : BalanceSpecification.MarkerExtension.wordCount_le_lastMarker_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:16.594872+00:00
-- url     : https://prove2.me/theorems/f78d3d30-b061-461b-991b-4ae8cc6f4934
-- title:
--   Marker Extension: word Count le last Marker sum
-- statement:
--   Partitioning by the last marker bounds every finite-word count in terms
--   of the boundary-word counts and the marker-free source language.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L77-L118
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L77-L118

module
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
public import Definitions.Def_BalanceSpecificaton_RenewalBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerWordBounds
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A] [Fintype A]
  [TopologicalSpace (Option A)] [DiscreteTopology (Option A)]
variable {Y : ShiftSpace A} (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)
omit [DiscreteTopology A]

theorem BalanceSpecification.MarkerExtension.wordCount_le_lastMarker_sum (n : ℕ) :
    wordCount (language (shift M hM x s)) n ≤ wordCount (language Y) n +
      ∑ k ∈ Finset.range n, (endingMarkerFinset (shift M hM x s) (k + 1)).card *
        wordCount (language Y) (n - (k + 1)) := by sorry
