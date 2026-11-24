-- Prove2me | Theorems.Thm_FFactor_exists_dart_of_notMem_Tset
-- name    : FFactor.exists_dart_of_notMem_Tset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T06:00:09.26457+00:00
-- url     : https://prove2.me/theorems/e70319c0-3bff-4864-9075-436182d361fd
-- title:
--   FFactor: exists dart of not Mem Tset
-- statement:
--   The FFactor construction uses the exists dart of not Mem Tset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L153-L158
-- source:
--   https://github.com/jtraverso/tutte-f-factor/blob/dc3bbce463c80c499d3e9fa072d13f9145d907d0/FFactorLib/FFactorSuff.lean#L153-L158

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}

theorem FFactor.exists_dart_of_notMem_Tset {v : V} (hv : v ∉ Tset G f U) :
    ∃ d : G.Dart, d.fst = v := by sorry
