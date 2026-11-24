-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_entropy_le_of_uniform_exp_bound
-- name    : BalanceSpecification.MarkerExtension.entropy_le_of_uniform_exp_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:19.610046+00:00
-- url     : https://prove2.me/theorems/81d1aaf6-572c-4f6d-a917-3a294ac6ffde
-- title:
--   Marker Extension: entropy le of uniform exp bound
-- statement:
--   A uniform exponential count envelope bounds the actual word-growth entropy.
--   This uses the already proved universal exponential lower bound, not an assumed
--   identification of a limsup or a provisional entropy value.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L229-L246
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L229-L246

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
omit [TopologicalSpace A] [DiscreteTopology A] [DiscreteTopology (Option A)]

theorem BalanceSpecification.MarkerExtension.entropy_le_of_uniform_exp_bound {Z : ShiftSpace (Option A)}
    (hZ : Z.carrier.Nonempty) {a K : ℝ}
    (hbound : ∀ n : ℕ, (wordCount (language Z) n : ℝ) ≤ K * Real.exp ((n : ℝ) * a)) :
    entropy Z hZ ≤ a := by sorry
