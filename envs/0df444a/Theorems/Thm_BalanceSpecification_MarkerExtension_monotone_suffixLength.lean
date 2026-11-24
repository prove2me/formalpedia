-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_monotone_suffixLength
-- name    : BalanceSpecification.MarkerExtension.monotone_suffixLength
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:02:27.554025+00:00
-- url     : https://prove2.me/theorems/7cc35613-a855-43e4-917a-385c74be63b5
-- title:
--   Marker Extension: monotone suffix Length
-- statement:
--   Strict increase of integer marker lengths makes their common suffix lengths
--   nondecreasing, including the subtraction endpoints.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L27-L34
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L27-L34

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

theorem BalanceSpecification.MarkerExtension.monotone_suffixLength (M : ℕ) {s : ℕ → ℕ} (hs : StrictMono s) :
    Monotone (suffixLength M s) := by sorry
