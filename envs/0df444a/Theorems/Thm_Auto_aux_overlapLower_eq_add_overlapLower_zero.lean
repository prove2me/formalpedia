-- Prove2me | Theorems.Thm_Auto_aux_overlapLower_eq_add_overlapLower_zero
-- name    : Auto.aux_overlapLower_eq_add_overlapLower_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:46.700313+00:00
-- url     : https://prove2.me/theorems/5b03ca83-aa99-4a4b-9574-1a30bee7f3c0
-- title:
--   Auto: aux overlap Lower eq add overlap Lower zero
-- statement:
--   Translating the lattice time translates the overlap's left endpoint.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L735-L742
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L735-L742

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem Auto.aux_overlapLower_eq_add_overlapLower_zero {n : ℕ}
    (hn : 0 < n) (ε : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapLower hn ε u m = (m : ℝ) + aux_overlapLower hn ε u 0 := by sorry
