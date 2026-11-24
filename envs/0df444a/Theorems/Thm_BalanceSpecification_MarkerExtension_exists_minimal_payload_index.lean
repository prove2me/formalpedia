-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_exists_minimal_payload_index
-- name    : BalanceSpecification.MarkerExtension.exists_minimal_payload_index
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:41.949641+00:00
-- url     : https://prove2.me/theorems/83640b09-0fa5-49c5-b94b-998257816430
-- title:
--   Marker Extension: exists minimal payload index
-- statement:
--   The first positive index whose payload length reaches a prescribed length.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L37-L43
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L37-L43

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

theorem BalanceSpecification.MarkerExtension.exists_minimal_payload_index {s : ℕ → ℕ}
    (hs : ∀ L : ℕ, ∃ n : ℕ, 1 ≤ n ∧ L ≤ s n) (l : ℕ) :
    ∃ m : ℕ, 1 ≤ m ∧ l ≤ s m ∧ ∀ n : ℕ, 1 ≤ n → l ≤ s n → m ≤ n := by sorry
