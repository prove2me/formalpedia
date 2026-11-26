-- Prove2me | Theorems.Thm_Auto_aux_orbit_add
-- name    : Auto.aux_orbit_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:36:47.44969+00:00
-- url     : https://prove2.me/theorems/3dd5d5e7-2d98-57da-955d-63f7eb775e56
-- title:
--   Auto: aux orbit add
-- statement:
--   Joint orbits turn addition of multi-indices into composition.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L141-L161
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L141-L161

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

theorem Auto.aux_orbit_add {X : Type*} : ∀ {n : ℕ} (S : Fin n → X → X)
    (_ : ∀ i j, Function.Commute (S i) (S j)) (k l : Fin n → ℕ),
    aux_orbit S (k + l) = aux_orbit S k ∘ aux_orbit S l
  := by sorry
