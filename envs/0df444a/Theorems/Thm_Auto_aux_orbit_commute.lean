-- Prove2me | Theorems.Thm_Auto_aux_orbit_commute
-- name    : Auto.aux_orbit_commute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:38:44.943272+00:00
-- url     : https://prove2.me/theorems/a12a1e3b-cf9f-56f3-98e6-2bdefe86e832
-- title:
--   Auto: aux orbit commute
-- statement:
--   A map commuting with every generator also commutes with their joint
--   orbit.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L125-L138
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L125-L138

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

theorem Auto.aux_orbit_commute {X : Type*} : ∀ {n : ℕ}
    (S : Fin n → X → X) (k : Fin n → ℕ) (h : X → X)
    (_hcomm : ∀ i, Function.Commute h (S i)),
      Function.Commute h (aux_orbit S k)
  := by sorry
