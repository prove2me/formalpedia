-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_rightBalanced_of_marker_extension_bound
-- name    : BalanceSpecification.MarkerExtension.rightBalanced_of_marker_extension_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:14.493275+00:00
-- url     : https://prove2.me/theorems/9950b842-c97a-4678-bce1-9c1f8c133db9
-- title:
--   Marker Extension: right Balanced of marker extension bound
-- statement:
--   The right-balanced lower bound transfers from the source whenever the
--   extension has a uniform exponential word-count envelope. All construction
--   properties are explicit and are proved separately for the literal marker code.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L92-L123
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L92-L123

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerRight
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*}
variable [TopologicalSpace A] [TopologicalSpace (Option A)]
  {Y : ShiftSpace A} {X : ShiftSpace (Option A)}
variable [Fintype A]

theorem BalanceSpecification.MarkerExtension.rightBalanced_of_marker_extension_bound
    (hX : X.carrier.Nonempty) (hY : Y.carrier.Nonempty) {C : ℝ} (hC : 0 < C)
    (hUpper : ∀ n : ℕ, (wordCount (language X) n : ℝ) ≤
      C * Real.exp ((n : ℝ) * entropy Y hY))
    (hYRight : RightBalanced (language Y))
    (hmarker : IsSynchronizing (language X) [none])
    (hF : ∀ v ∈ language Y, [none] ++ v.map some ∈ language X)
    (hNonMarker : ∀ u ∈ language X, none ∉ u →
      ∃ v ∈ language Y, u = v.map some) : RightBalanced (language X) := by sorry
