-- Prove2me | Theorems.Thm_Auto_aux_orbit_add_coordinate_apply
-- name    : Auto.aux_orbit_add_coordinate_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:40:41.026625+00:00
-- url     : https://prove2.me/theorems/6878d5e7-6cb5-5657-8bfd-fadffd9b9faa
-- title:
--   Auto: aux orbit add coordinate apply
-- statement:
--   The Auto construction uses the aux orbit add coordinate apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1099-L1111
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L1099-L1111

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

theorem Auto.aux_orbit_add_coordinate_apply {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {n : ℕ}
    (S : ErgodicSystem X μ n) (k : Fin n → ℕ) (i : Fin n)
    (m : ℕ) (x : X) :
    aux_orbit S.transformation (k + aux_coordinate i m) x =
      (S.transformation i)^[m] (aux_orbit S.transformation k x) := by sorry
