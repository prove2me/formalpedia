-- Prove2me | Theorems.Thm_BalanceSpecification_marker_count_lower_bound_of_leftBalanced
-- name    : BalanceSpecification.marker_count_lower_bound_of_leftBalanced
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:22.022302+00:00
-- url     : https://prove2.me/theorems/84fbc705-b38f-44a9-ad1c-8f0ea80a87dd
-- title:
--   Balance Specification: marker count lower bound of left Balanced
-- statement:
--   Left-balancedness would give a linearly growing multiple of the base
--   entropy exponential, by the actual last-marker injections above.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L108-L153
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L108-L153

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_TwoSidedCounts
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerNonleft
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A] [TopologicalSpace A] [TopologicalSpace (Option A)]

theorem BalanceSpecification.marker_count_lower_bound_of_leftBalanced
    {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty)
    (hs : IsSynchronizing (language X) [none])
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X)
    (hleft : LeftBalanced (language X)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * c * Real.exp ((n : ℝ) * entropy Y hY) ≤
        wordCount (language X) (n + 1) := by sorry
