-- Prove2me | Theorems.Thm_BalanceSpecification_MarkerExtension_exists_last_marker_split
-- name    : BalanceSpecification.MarkerExtension.exists_last_marker_split
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:04:10.007333+00:00
-- url     : https://prove2.me/theorems/1ed4930d-c938-4be0-962c-7a8bf4311cf2
-- title:
--   Marker Extension: exists last marker split
-- statement:
--   Split a word immediately after its last fresh marker.
--
--   Source: https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L19-L30
-- source:
--   https://github.com/pseudorandom/balance_and_specification/blob/62771ced95e6f431064d40780b623362263ae9e4/BalanceSpecificaton/MarkerRight.lean#L19-L30

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

theorem BalanceSpecification.MarkerExtension.exists_last_marker_split {u : Word (Option A)} (hu : none ∈ u) :
    ∃ p q : Word (Option A), u = p ++ none :: q ∧ none ∉ q := by sorry
