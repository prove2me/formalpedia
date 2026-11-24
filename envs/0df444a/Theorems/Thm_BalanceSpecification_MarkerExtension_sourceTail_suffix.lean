-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_sourceTail_suffix
-- name    : BalanceSpecification.MarkerExtension.sourceTail_suffix
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:02:40.274937+00:00
-- url     : https://prove2.me/theorems/a4fb592b-d0cd-4d81-9c22-30e1baa467c7
-- title:
--   Marker Extension: source Tail suffix
-- statement:
--   The source's past blocks are nested as suffixes.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L18-L23
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerSuffix.lean#L18-L23

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

theorem BalanceSpecification.MarkerExtension.sourceTail_suffix (x : Y.carrier) {m n : ℕ} (hmn : m ≤ n) :
    sourceTail x m <:+ sourceTail x n := by sorry
