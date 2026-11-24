-- Prove2me | Theorems.Thm_BalanceSpecification_markerPair_count_le
-- name    : BalanceSpecification.markerPair_count_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:04:17.939949+00:00
-- url     : https://prove2.me/theorems/96abee9f-ef88-4000-a767-5b0fd4505acb
-- title:
--   Balance Specification: marker Pair count le
-- statement:
--   The Balance Specification construction uses the marker Pair count le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L37-L90
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerNonleft.lean#L37-L90

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

theorem BalanceSpecification.markerPair_count_le {X : ShiftSpace (Option A)} {Y : ShiftSpace A}
    (hs : IsSynchronizing (language X) [none])
    (hext : ∀ v ∈ language Y, none :: v.map some ∈ language X) (n : ℕ) :
    (∑ k : Fin n, (predecessorFinset (language X) [none] (k.val + 1)).card *
      wordCount (language Y) (n - 1 - k.val)) ≤ wordCount (language X) (n + 1) := by sorry
