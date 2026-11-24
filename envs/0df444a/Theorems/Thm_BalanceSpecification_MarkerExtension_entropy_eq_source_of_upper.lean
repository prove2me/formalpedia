-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_entropy_eq_source_of_upper
-- name    : BalanceSpecification.MarkerExtension.entropy_eq_source_of_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:03:41.177192+00:00
-- url     : https://prove2.me/theorems/97455235-bbc3-4612-a686-1511bf3b3ee1
-- title:
--   Marker Extension: entropy eq source of upper
-- statement:
--   For the actual code, the upper envelope combines with its proved source
--   inclusion to give equality of entropies.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L250-L255
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerWordBounds.lean#L250-L255

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

theorem BalanceSpecification.MarkerExtension.entropy_eq_source_of_upper {hY : Y.carrier.Nonempty} {K : ℝ}
    (hbound : ∀ n : ℕ, (wordCount (language (shift M hM x s)) n : ℝ) ≤
      K * Real.exp ((n : ℝ) * entropy Y hY)) :
    entropy (shift M hM x s) (shift_nonempty M hM x s) = entropy Y hY := by sorry
