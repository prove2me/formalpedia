-- Prove2me | Theorems.Thm_Auto_aux_orbit_add_coordinate
-- name    : Auto.aux_orbit_add_coordinate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:45:25.9148+00:00
-- url     : https://prove2.me/theorems/4de5e79d-bb2c-4a6b-8bed-b5708893883f
-- title:
--   Auto: aux orbit add coordinate
-- statement:
--   Shifting a joint orbit in one coordinate amounts to composing with the
--   corresponding transformation iterate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L227-L231
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L227-L231

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

theorem Auto.aux_orbit_add_coordinate {X : Type*} {n : ℕ}
    (S : Fin n → X → X) (hS : ∀ i j, Function.Commute (S i) (S j))
    (k : Fin n → ℕ) (i : Fin n) (m : ℕ) :
    aux_orbit S (k + aux_coordinate i m) = aux_orbit S k ∘ (S i)^[m] := by sorry
