-- Prove2me | Theorems.Thm_FFactor_notMem_U_of_home
-- name    : FFactor.notMem_U_of_home
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:01:49.966903+00:00
-- url     : https://prove2.me/theorems/9003feaa-91be-4fca-a512-2bf753b32734
-- title:
--   FFactor: not Mem U of home
-- statement:
--   The FFactor construction uses the not Mem U of home property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L110-L120
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorCount.lean#L110-L120

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}

theorem FFactor.notMem_U_of_home {hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x} {a : GV G f}
    (ha : home G f U a ∉ Sset G f U ∪ Tset G f U) : a ∉ U := by sorry
