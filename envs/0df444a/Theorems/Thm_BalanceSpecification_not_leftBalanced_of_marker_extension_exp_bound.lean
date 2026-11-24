-- Prove2me | Theorems.Thm_BalanceSpecification_not_leftBalanced_of_marker_extension_exp_bound
-- name    : BalanceSpecification.not_leftBalanced_of_marker_extension_exp_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:37.072046+00:00
-- url     : https://prove2.me/theorems/2c7f694b-5727-4de0-b230-a1b052916d08
-- title:
--   Balance Specification: not left Balanced of marker extension exp bound
-- statement:
--   The last-marker contradiction used in the source construction. This is an
--   internal construction lemma: its synchronizing, extension, and count hypotheses
--   must all be established for the actual constructed shift before applying it.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L158-L185
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L158-L185

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

theorem BalanceSpecification.not_leftBalanced_of_marker_extension_exp_bound
    {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty)
    (hs : IsSynchronizing (language X) [none])
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X)
    {C : ℝ} (hC : 0 < C)
    (hupper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy Y hY)) :
    ¬ LeftBalanced (language X) := by sorry
