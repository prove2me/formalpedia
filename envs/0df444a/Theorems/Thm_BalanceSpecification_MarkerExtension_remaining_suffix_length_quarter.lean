-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_remaining_suffix_length_quarter
-- name    : BalanceSpecification.MarkerExtension.remaining_suffix_length_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:38.534701+00:00
-- url     : https://prove2.me/theorems/7dbbc81c-1ca9-4ea7-a9c2-79b4fd1c036c
-- title:
--   Marker Extension: remaining suffix length quarter
-- statement:
--   The sparse construction leaves at most one quarter of a suffix outside
--   its common tail. This is a direct arithmetic consequence of the chosen lengths.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L47-L53
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L47-L53

module
public import Definitions.Def_BalanceSpecificaton_MarkerExtension
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_MarkerSuffix
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification BalanceSpecification.MarkerExtension
variable {A : Type*} [TopologicalSpace A] {Y : ShiftSpace A}

theorem BalanceSpecification.MarkerExtension.remaining_suffix_length_quarter (M : ℕ) (s : ℕ → ℕ)
    (hsize : ∀ n : ℕ, 1 ≤ n → 4 * (n + M) ≤ s n)
    {l m : ℕ} (hm : 1 ≤ m) (hml : l ≤ s m) :
    4 * (l - min l (suffixLength M s m)) ≤ l := by sorry
