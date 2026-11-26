-- Prove2me | Theorems.Thm_Auto_aux_orbit_single
-- name    : Auto.aux_orbit_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:45:28.95309+00:00
-- url     : https://prove2.me/theorems/69e3d1c7-8fac-4b93-bb2c-7e462673d970
-- title:
--   Auto: aux orbit single
-- statement:
--   A joint orbit with only one nonzero coordinate is the corresponding
--   iterate.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L167-L197
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L167-L197

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

theorem Auto.aux_orbit_single {X : Type*} : ∀ {n : ℕ}
    (S : Fin n → X → X) (i : Fin n) (r : ℕ),
    aux_orbit S (Pi.single i r) = (S i)^[r]
  := by sorry
