-- Prove2me | Theorems.Thm_Auto_aux_orbit_coordinate
-- name    : Auto.aux_orbit_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:37:05.64092+00:00
-- url     : https://prove2.me/theorems/f0beae51-ea35-4db2-b284-a06796392da3
-- title:
--   Auto: aux orbit coordinate
-- statement:
--   The Auto construction uses the aux orbit coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L203-L221
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L203-L221

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

theorem Auto.aux_orbit_coordinate {X : Type*} : ∀ {n : ℕ}
    (S : Fin n → X → X) (i : Fin n) (m : ℕ),
    aux_orbit S (aux_coordinate i m) = (S i)^[m]
  := by sorry
