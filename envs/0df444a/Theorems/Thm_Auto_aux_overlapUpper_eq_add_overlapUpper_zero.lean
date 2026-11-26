-- Prove2me | Theorems.Thm_Auto_aux_overlapUpper_eq_add_overlapUpper_zero
-- name    : Auto.aux_overlapUpper_eq_add_overlapUpper_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:45.364501+00:00
-- url     : https://prove2.me/theorems/cc2c9a10-7cc6-5fd6-8ce6-526b67412f44
-- title:
--   Auto: aux overlap Upper eq add overlap Upper zero
-- statement:
--   Translating the lattice time translates the overlap's right endpoint.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L745-L752
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L745-L752

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

theorem Auto.aux_overlapUpper_eq_add_overlapUpper_zero {n : ℕ}
    (hn : 0 < n) (ε δ : ℝ) (u : aux_RVector n) (m : ℕ) :
    aux_overlapUpper hn ε δ u m = (m : ℝ) + aux_overlapUpper hn ε δ u 0 := by sorry
