-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_code_wordFinset_eq_index_union
-- name    : BalanceSpecification.MarkerExtension.code_wordFinset_eq_index_union
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:03:48.710155+00:00
-- url     : https://prove2.me/theorems/784d5ed2-4391-4926-aeba-823be426ee8e
-- title:
--   Marker Extension: code word Finset eq index union
-- statement:
--   For each tested length, every source generator belongs to a finite union
--   of its actual positive-index families.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L82-L109
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerCodeCounts.lean#L82-L109

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Definitions.Def_BalanceSpecificaton_MarkerEstimates
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerCodeCounts
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
open scoped Classical
variable {A : Type*} [TopologicalSpace A] [Fintype A] {Y : ShiftSpace A}
variable (M : ℕ)
  (hM : ∀ u ∈ language Y, ∀ v ∈ language Y,
    ∃ b ∈ language Y, b.length = M ∧ u ++ b ++ v ∈ language Y)
  (x : Y.carrier) (s : ℕ → ℕ)

theorem BalanceSpecification.MarkerExtension.code_wordFinset_eq_index_union
    (hs : ∀ n : ℕ, 1 ≤ n → n + M ≤ s n) {l N : ℕ} (hlN : l ≤ N) :
    wordFinset (code M hM x s) (l + 1) =
      (Finset.range (N + 1)).biUnion
        (fun n => if s n = l then sourceCodeFinsetAt M hM x s n else ∅) := by sorry
