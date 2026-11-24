-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_endingMarker_count_le_convolution
-- name    : BalanceSpecification.MarkerExtension.endingMarker_count_le_convolution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:08.662649+00:00
-- url     : https://prove2.me/theorems/fafebad0-d3fa-4eb3-bc75-c4884440586c
-- title:
--   Marker Extension: ending Marker count le convolution
-- statement:
--   The boundary normal form gives an upper convolution count, using actual
--   source-payload suffixes and actual finite code concatenations.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L38-L72
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L38-L72

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

theorem BalanceSpecification.MarkerExtension.endingMarker_count_le_convolution (n : ℕ) :
    (endingMarkerFinset (shift M hM x s) (n + 1)).card ≤
      ∑ l ∈ Finset.range (n + 1), (payloadSuffixFinset M hM x s l).card *
        wordCount (generatedWords (code M hM x s)) (n - l) := by sorry
